module

public import Mathlib
public import Erdos99.Part04RoundnessAndConnectivity
public import Erdos99.Part05FacesAndShores
public import Erdos99.Part06TokensHopsCaps
public import Erdos99.Part07StabilityAndCharging
public import Erdos99.Part08Saturation

/-!
# Erdős Problem 99 under finite multiplicity — Part 9 of 9: Capless and flagged exclusions, and assembly of the track count

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `CaplessPinning`
* `CaplessCount`
* `CaplessG`
* `CaplessGMain`
* `CaplessGFew`
* `CaplessKGeometry`
* `CaplessKElim`
* `CaplessKPoly`
* `CaplessKPinning`
* `CaplessKPorts`
* `CaplessKMain`
* `CaplessKFew`
* `CaplessSmall`
* `UnflaggedMargin`
* `FlaggedPoly`
* `FlaggedPinning`
* `FlaggedGeometry`
* `FlaggedCount`
* `FlaggedExclusion`
* `ChargingCutoff`
* `TrackCountAssembly`
* `CountingWitnessReduction`
* `Final`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessPinning`
-/

section CaplessPinning

/-!
# Approximate component relations pin the direction (Verification Guide §12.4, §13.4)

The approximate form of `capless_solutions_card_le`, by compactness:

* `CapData m`: the data `(k₀, Z₀, k, Z)` of a component relation with `m` responses;
* `capAdm m R`: the compact set of admissible data (`1 ≤ k₀ ≤ R`, `‖Z₀‖ ≤ R`, `k_i ∈ {1, 2}`,
  `‖Z_i‖ ≤ R`);
* `CapApprox m r d ζ`: unit vectors `p_i, u_i` satisfy the relations
  `k₀ ζ + Z₀ + Σ p_i ≈ 0`, `k_i ζ + Z_i - p_i + u_i ≈ 0` up to `r`;
* `capless_pinning`: for every separation `w > 0` there are `r, μ > 0` such that, for every centre
  `c`, a `w`-separated set of unit directions each admitting an `r`-approximate solution with
  admissible data `μ`-close to `c` has at most `capDeg m` elements.
-/

open Filter Topology Metric

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessElim

/-- The data `(k₀, Z₀, k, Z)` of a component relation with `m` responses. -/
abbrev CapData (m : ℕ) : Type := ℝ × ℂ × (Fin m → ℝ) × (Fin m → ℂ)

/-- The admissible data. -/
def capAdm (m : ℕ) (R : ℝ) : Set (CapData m) :=
  Set.Icc 1 R ×ˢ closedBall 0 R ×ˢ Set.univ.pi (fun _ => ({1, 2} : Set ℝ)) ×ˢ
    Set.univ.pi (fun _ => closedBall (0 : ℂ) R)

lemma isCompact_capAdm (m : ℕ) (R : ℝ) : IsCompact (capAdm m R) :=
  isCompact_Icc.prod ((isCompact_closedBall _ _).prod
    ((isCompact_univ_pi fun _ => (Set.toFinite _).isCompact).prod
      (isCompact_univ_pi fun _ => isCompact_closedBall _ _)))

/-- The residuals of the component relations. -/
def capRes0 {m : ℕ} (d : CapData m) (ζ : ℂ) (p : Fin m → ℂ) : ℝ :=
  ‖(d.1 : ℂ) * ζ + d.2.1 + ∑ i, p i‖

def capRes1 {m : ℕ} (d : CapData m) (ζ : ℂ) (p u : Fin m → ℂ) (i : Fin m) : ℝ :=
  ‖(d.2.2.1 i : ℂ) * ζ + d.2.2.2 i - p i + u i‖

/-- `r`-approximate unit solutions of the component relations at the direction `ζ`. -/
def CapApprox (m : ℕ) (r : ℝ) (d : CapData m) (ζ : ℂ) : Prop :=
  ∃ p u : Fin m → ℂ, (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1) ∧ capRes0 d ζ p < r ∧ ∀ i, capRes1 d ζ p u i < r

/-- Exact solutions for admissible data lie in a set of at most `capDeg m` directions. -/
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

/-- The state of one approximate solution: data, direction and unit vectors. -/
abbrev CapState (m : ℕ) : Type := CapData m × ℂ × (Fin m → ℂ) × (Fin m → ℂ)

/-- The compact set of admissible states. -/
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

/-- **Approximate component relations pin the direction** (compactness, Verification Guide
§12.4). -/
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
  -- all limit data agree
  have hdata : ∀ j, (a j).1 = (a 0).1 := by
    intro j
    have ht : Tendsto (fun n => (s (φ n) j).1 - (s (φ n) 0).1) atTop (𝓝 ((a j).1 - (a 0).1)) :=
      ((continuous_fst.tendsto _).comp (hlimj j)).sub ((continuous_fst.tendsto _).comp (hlimj 0))
    have ht0 : Tendsto (fun n => (s (φ n) j).1 - (s (φ n) 0).1) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (hsd (φ n) j 0).le) ?_
      simpa [mul_one_div] using hinv.const_mul 2
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
  -- the limit directions are exact solutions for the common data
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
    simp only at h
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

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessCount`
-/

section CaplessCount

/-!
# Hull directions pinned by component relations are few (Verification Guide §12.5, §13.4)

* `exists_maximal_separated`: a finite set contains a `w`-separated subset that is `w`-dense in it;
* `capless_directions_few`: for a bounded number `Nc` of data centres and every `ε > 0` there are
  tolerances `r, μ > 0` such that, eventually, every set of hull sides whose directions admit
  `r`-approximate solutions of the component relations, with admissible data `μ`-close to one of
  the centres, has at most `ε D` elements.
-/

open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace CaplessElim

/-- A finite set contains a `w`-separated subset every point of the set is `w`-close to. -/
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

/-- **Hull directions pinned by the component relations are few.** -/
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
  -- the directions near each centre
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

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessG`
-/

section CaplessG

/-!
# Small capless components of `G` are few (Verification Guide §13.4, the `G` part)

* `component_data`: at a set `Cf` of good faces all of whose unmarked short ports are matched and
  whose outgoing ports end at degree-two faces, the outgoing port vectors `p_i` and the unit
  vectors `u_i` of the receiving faces satisfy the component relations
  `k₀ ζ + Z₀ + Σ p_i ≈ 0`, `k_i ζ + Z_i - p_i + u_i ≈ 0` (with `ζ` the label direction of one face
  of `Cf`);
* `capless_G_few`: the number of stubless components of the subgraph on `G` (the faces of degree
  `≠ 2`) with at most `M` faces is at most `ε D`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim

/-- The data of the component relations of a set of faces `Cf` with outgoing ports enumerated by
`e`. -/
def compData {X : Finset Plane} (L : ℝ) (G : GoodFaces X) (Cf : Finset (Set ℂ))
    {Ext : Finset (Set ℂ × Sym2 Plane)} {m : ℕ} (e : Ext ≃ Fin m) : CapData m :=
  (∑ F ∈ Cf, G.kMult F, ∑ F ∈ Cf, longSum X L F,
    fun i => G.kMult (trackMate X (e.symm i)).1, fun i => longSum X L (trackMate X (e.symm i)).1)

/-- **The component relations at a capless set of faces.** -/
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

/-! ## Centres of the component data -/

/-- The sums `Σ_u f(u) u` with multiplicities `f(u) ≤ K`. -/
def sumCentresK (U : Finset ℂ) (K : ℕ) : Finset ℂ :=
  (Finset.univ : Finset (U → Fin (K + 1))).image (fun f => ∑ u : U, ((f u : ℕ) : ℂ) * (u : ℂ))

lemma card_sumCentresK_le (U : Finset ℂ) (K : ℕ) : (sumCentresK U K).card ≤ (K + 1) ^ U.card := by
  refine Finset.card_image_le.trans ?_
  simp

/-- A sum of at most `K` vectors, each within `ε` of `U`, lies within `K ε` of `sumCentresK U K`. -/
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

/-- The centres of the component data with `m` responses. -/
def capCentres (U : Finset ℂ) (M m : ℕ) : Finset (CapData m) :=
  ((Finset.range (2 * M + 1)).image (fun j : ℕ => (j : ℝ))) ×ˢ sumCentresK U (6 * M) ×ˢ
    Fintype.piFinset (fun _ : Fin m => ({1, 2} : Finset ℝ)) ×ˢ
    Fintype.piFinset (fun _ : Fin m => sumCentresK U 6)

/-- The bound on the number of centres. -/
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

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessGMain`
-/

section CaplessGMain

/-!
# Small capless components of `G` are few: assembly (Verification Guide §13.4)

* `component_witness`: a capless set of faces away from the exceptional faces of the clustering
  produces admissible component data close to a centre, with an approximate solution at the label
  direction of any of its faces;
* `capless_G_few`: the number of stubless components of the subgraph on `G` with at most `M` faces
  is at most `ε D`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim

/-- The outgoing unmarked short ports of a set of faces. -/
def extPorts (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (Cf : Finset (Set ℂ)) : Finset (Set ℂ × Sym2 Plane) :=
  (unmarkedPorts X L G mk).filter (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf)

/-- **A capless set of faces gives a pinned direction.** -/
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
  -- the centre of the outer long sides
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
  -- the centres of the receiving faces
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
    linarith
  · linarith [h1 i]

end Erdos99
end

end CaplessGMain

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessGFew`
-/

section CaplessGFew

/-!
# Small capless components of `G` are few (Verification Guide §13.4)

* `card_ports_in_le`, `card_extPorts_le`: a set of `k` good faces has at most `4 k` unmarked short
  ports;
* `card_excComp_le`: the components meeting a set `Bad`, or matched into it, number at most
  `5 · #Bad`;
* `stubless_component_facts`: the faces of a small stubless component of the subgraph on `U`;
* `capless_G_few`: the stubless components of the subgraph on `G` with at most `M` faces number at
  most `ε D`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

/-- A set of `k` faces carries at most `4 k` unmarked short ports. -/
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

/-- The components meeting `Bad` or matched into `Bad` number at most `5 · #Bad`. -/
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

/-- **The faces of a small stubless component.** -/
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


/-- Splitting a finite set by a bounded natural-valued function. -/
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


/-- **Small capless components of `G` are few** (Verification Guide §13.4, the part `G`).  For
every `M` and `ε, λ > 0` there are a saturation tolerance and a cutoff fraction `a₀` such that for
every cutoff fraction `a ≤ a₀`, eventually every saturated marking with the degree window has at
most `ε D` stubless components of the subgraph on the faces of degree `≠ 2` with at most `M`
faces. -/
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
  -- the parameter inequalities
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
  -- the components
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

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessKGeometry`
-/

section CaplessKGeometry

/-!
# Capless components of `K`: the geometry of `J` neighbours (Verification Guide §13.4)

* `three_unit_sum_lb`: **three-port margin**: three unit vectors whose projections on a unit
  tangent are at most `1/2 - κ` have a sum of norm at least `min 1 κ`;
* `J_face_equation`: the closure equation at a degree-three face, given two of its unmarked short
  ports;
* `ext_J_equation`: the response relation at a `J` neighbour: if a matched port `q` ends at a `J`
  face and `q'` is another matched port of that face, then
  `‖k τ - portVec q + portVec q' + u + Z‖ ≤ tol` for a unit vector `u`;
* `exists_H_incidence`: a `J` face has a matched port whose mate is a degree-two face;
* `card_longSides_J`, `card_longSides_H`: a `J` face has exactly one long side, a degree-two face
  none or two;
* `JH_margin`: the long-side sums `Z` of a `J` face and `W` of a degree-two face satisfy
  `‖Z‖ ≥ min 1 κ` and `‖Z + W‖ ≥ min 1 κ` when all their long sides have projection `≤ 1/2 - κ`.
-/

open scoped BigOperators Real
open Filter ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

/-! ## The three-port margin -/

lemma re_sq_of_norm_one {y : ℂ} (hy : ‖y‖ = 1) : (y ^ 2).re = 2 * y.re ^ 2 - 1 := by
  have h := Complex.sq_norm y
  rw [hy, Complex.normSq_apply] at h
  rw [pow_two, Complex.mul_re]
  nlinarith

/-- **Three unit vectors with projections at most `1/2 - κ` do not nearly cancel.** -/
lemma three_unit_sum_lb {κ : ℝ} (hκ : 0 < κ) {τ y1 y2 y3 : ℂ} (hτ : ‖τ‖ = 1) (h1 : ‖y1‖ = 1)
    (h2 : ‖y2‖ = 1) (h3 : ‖y3‖ = 1) (m1 : (y1 * conj τ).re ≤ 1 / 2 - κ)
    (m2 : (y2 * conj τ).re ≤ 1 / 2 - κ) (m3 : (y3 * conj τ).re ≤ 1 / 2 - κ) :
    min 1 κ ≤ ‖y1 + y2 + y3‖ := by
  set x1 := y1 * conj τ
  set x2 := y2 * conj τ
  set x3 := y3 * conj τ
  have hn : ∀ y : ℂ, ‖y‖ = 1 → ‖y * conj τ‖ = 1 := fun y hy => by
    rw [norm_mul, Complex.norm_conj, hy, hτ, one_mul]
  have n1 := hn y1 h1
  have n2 := hn y2 h2
  have n3 := hn y3 h3
  have hS : ‖y1 + y2 + y3‖ = ‖x1 + x2 + x3‖ := by
    rw [show x1 + x2 + x3 = (y1 + y2 + y3) * conj τ by ring, norm_mul, Complex.norm_conj, hτ,
      mul_one]
  rw [hS]
  set S := x1 + x2 + x3 with hSdef
  set δ := ‖S‖
  by_contra hcon
  push_neg at hcon
  have hδ1 : δ < 1 := lt_of_lt_of_le hcon (min_le_left _ _)
  have hδκ : δ < κ := lt_of_lt_of_le hcon (min_le_right _ _)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hc : ∀ x : ℂ, ‖x‖ = 1 → conj x * x = 1 := fun x hx => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hx]; norm_num
  -- the sum of squares
  have he2 : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = S ^ 2 - 2 * (x1 * x2 * x3) * conj S := by
    rw [hSdef, map_add, map_add]
    linear_combination (2 * x2 * x3) * hc x1 n1 + (2 * x1 * x3) * hc x2 n2 +
      (2 * x1 * x2) * hc x3 n3
  have hsq : ‖x1 ^ 2 + x2 ^ 2 + x3 ^ 2‖ ≤ δ ^ 2 + 2 * δ := by
    rw [he2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_mul, norm_mul, norm_mul, norm_mul, n1, n2, n3, Complex.norm_conj]
    norm_num
    exact le_rfl
  have hre2 : -(δ ^ 2 + 2 * δ) ≤ (x1 ^ 2 + x2 ^ 2 + x3 ^ 2).re := by
    have := Complex.abs_re_le_norm (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)
    linarith [neg_abs_le (x1 ^ 2 + x2 ^ 2 + x3 ^ 2).re]
  rw [Complex.add_re, Complex.add_re, re_sq_of_norm_one n1, re_sq_of_norm_one n2,
    re_sq_of_norm_one n3] at hre2
  have hreS : -δ ≤ x1.re + x2.re + x3.re := by
    have := Complex.abs_re_le_norm S
    rw [hSdef, Complex.add_re, Complex.add_re] at this
    linarith [neg_abs_le (x1.re + x2.re + x3.re)]
  have hb : ∀ x : ℂ, ‖x‖ = 1 → -1 ≤ x.re := fun x hx => by
    have := Complex.abs_re_le_norm x
    rw [hx] at this
    linarith [neg_abs_le x.re]
  have b1 := hb x1 n1
  have b2 := hb x2 n2
  have b3 := hb x3 n3
  have t1 : κ * (x1.re + 1) ≤ (x1.re + 1) * (1 / 2 - x1.re) := by nlinarith
  have t2 : κ * (x2.re + 1) ≤ (x2.re + 1) * (1 / 2 - x2.re) := by nlinarith
  have t3 : κ * (x3.re + 1) ≤ (x3.re + 1) * (1 / 2 - x3.re) := by nlinarith
  have hsum_re : x1.re + x2.re + x3.re ≤ δ := by
    have := Complex.abs_re_le_norm S
    rw [hSdef, Complex.add_re, Complex.add_re] at this
    linarith [le_abs_self (x1.re + x2.re + x3.re)]
  nlinarith

/-! ## The closure equation at a degree-three face -/

/-- **The closure equation at a degree-three face**: given two distinct unmarked short ports
`e₁, e₂` of a good face `F` of degree three, with oriented sides `ab₁, ab₂`, the third unmarked
short port gives a unit vector `u` with `‖k τ + (b₁ - a₁) + (b₂ - a₂) + u + Z‖ ≤ tol`. -/
theorem J_face_equation :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ F ∈ G.good, (trackGraph X L G mk).deg F = 3 →
      ∀ e1 ∈ shortPorts X L F \ mk F, ∀ e2 ∈ shortPorts X L F \ mk F, e1 ≠ e2 →
      ∀ ab1 ∈ orientedSides X F, Sym2.map toC e1 = s(ab1.1, ab1.2) →
      ∀ ab2 ∈ orientedSides X F, Sym2.map toC e2 = s(ab2.1, ab2.2) →
        ∃ u : ℂ, ‖u‖ = 1 ∧ ‖(G.kMult F : ℂ) * labDir lab F + (ab1.2 - ab1.1) + (ab2.2 - ab2.1) +
          u + longSum X L F‖ ≤ tol := by
  filter_upwards [card_trackEnds, markedSum_short_add_longSum, card_filter_orientedSides,
    face_side_facts] with n hends hzero hcardf hside hfm X hX htri L tol G mk lab hmk hlab F hFg
    hdeg3 e1 he1 e2 he2 hne ab1 hab1 hmap1 ab2 hab2 hmap2
  have hdeg := hdeg3
  rw [trackGraph_deg (hends hfm X hX htri) L G mk hFg] at hdeg
  have hsub := (hmk F hFg).1
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX.1.2).1 (G.good_subset hFg)
  set N := shortPorts X L F \ mk F with hN
  have hports : ∀ f ∈ N, IsPort X (Sum.inl F) f :=
    fun f hf => (Finset.mem_filter.1 (Finset.sdiff_subset hf)).2.1
  set S := (orientedSides X F).filter (fun ab => ∃ f ∈ N, Sym2.map toC f = s(ab.1, ab.2)) with hS
  have hc : S.card = 3 := by rw [hS, hcardf hfm X hX F hFe N hports, hdeg]
  have h1S : ab1 ∈ S := Finset.mem_filter.2 ⟨hab1, e1, he1, hmap1⟩
  have h2S : ab2 ∈ S := Finset.mem_filter.2 ⟨hab2, e2, he2, hmap2⟩
  have h12 : ab1 ≠ ab2 := by
    intro h
    apply hne
    rw [h] at hmap1
    exact Sym2.map.injective toC.injective (hmap1.trans hmap2.symm)
  have h2S' : ab2 ∈ S.erase ab1 := Finset.mem_erase.2 ⟨h12.symm, h2S⟩
  have hc1 : ((S.erase ab1).erase ab2).card = 1 := by
    rw [Finset.card_erase_of_mem h2S', Finset.card_erase_of_mem h1S, hc]
  obtain ⟨t, ht⟩ := Finset.card_eq_one.1 hc1
  have htS : t ∈ S := by
    have : t ∈ (S.erase ab1).erase ab2 := by rw [ht]; exact Finset.mem_singleton_self t
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
  have hts : t ∈ orientedSides X F := (Finset.mem_filter.1 htS).1
  have hNsum : markedSum X F N = (ab1.2 - ab1.1) + (ab2.2 - ab2.1) + (t.2 - t.1) := by
    rw [markedSum, ← hS, ← Finset.add_sum_erase S _ h1S, ← Finset.add_sum_erase _ _ h2S', ht,
      Finset.sum_singleton]
    ring
  have h0 := hzero hfm X hX L F hFe
  rw [← Finset.union_sdiff_of_subset hsub, markedSum_union Finset.disjoint_sdiff, ← hN,
    hNsum] at h0
  have hl := (hlab.2 F hFg).2.1
  rw [GoodFaces.markMult_eq] at hl
  refine ⟨t.2 - t.1, (hside hfm X hX G F hFg).2 t hts, ?_⟩
  calc _ = ‖-(markedSum X F (mk F) - (G.kMult F : ℂ) * toC (sideDir (lab F)))‖ := by
        congr 1; rw [labDir]; linear_combination h0
    _ ≤ tol := by rw [norm_neg]; exact hl

/-- **The response relation at a `J` neighbour.** -/
theorem ext_J_equation :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        (trackGraph X L G mk).deg (trackMate X q).1 = 3 →
      ∀ q' ∈ unmarkedPorts X L G mk, q'.1 = (trackMate X q).1 → q' ≠ trackMate X q →
        ∃ u : ℂ, ‖u‖ = 1 ∧ ‖(G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 -
          portVec X q + portVec X q' + u + longSum X L (trackMate X q).1‖ ≤ tol := by
  filter_upwards [J_face_equation, portVec_mate, exists_side_of_port] with n hface hmate hside hfm
    X hX htri L tol G mk lab hmk hlab q hq hm hdeg q' hq' hq'1 hne
  obtain ⟨hg', hsp', hnm'⟩ := mem_unmarkedPorts.1 hm.2
  obtain ⟨-, hp', -⟩ := Finset.mem_filter.1 hsp'
  obtain ⟨ab, hab, habe⟩ := hside hfm X hX _ _ hp'
  obtain ⟨hg'', hsp'', hnm''⟩ := mem_unmarkedPorts.1 hq'
  rw [hq'1] at hsp'' hnm''
  obtain ⟨-, hp'', -⟩ := Finset.mem_filter.1 hsp''
  obtain ⟨ab', hab', habe'⟩ := hside hfm X hX _ _ hp''
  have hne2 : (trackMate X q).2 ≠ q'.2 := by
    intro h; apply hne; exact Prod.ext hq'1 h.symm
  obtain ⟨u, hu, h⟩ := hface hfm X hX htri L tol G mk lab hmk hlab _ hg' hdeg _
    (Finset.mem_sdiff.2 ⟨hsp', hnm'⟩) _ (Finset.mem_sdiff.2 ⟨hsp'', hnm''⟩) hne2 ab hab habe
    ab' hab' habe'
  refine ⟨u, hu, ?_⟩
  have hne' : (trackMate X q).1.Nonempty :=
    nonempty_of_mem_exceptionalFaces ((mem_exceptionalFinset hX.1.2).1 (G.good_subset hg'))
  have hv : ab.2 - ab.1 = -portVec X q := by
    rw [← portVec_eq hne' hab habe, hmate hfm X hX htri L G mk q hq hm]
  have hv' : ab'.2 - ab'.1 = portVec X q' := by
    rw [← portVec_eq (q := q') (by rw [hq'1]; exact hne') (by rw [hq'1]; exact hab') habe']
  rw [hv, hv', ← sub_eq_add_neg] at h
  exact h

/-- **A `J` face has a matched port ending at a degree-two face.** -/
lemma exists_H_incidence {X : Finset Plane} (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)} {F : Set ℂ}
    (hF : F ∈ (trackGraph X L G mk).Js G.good) :
    ∃ q' ∈ unmarkedPorts X L G mk, q'.1 = F ∧ TrackMated X L G mk q' ∧
      (trackMate X q').1 ∈ (trackGraph X L G mk).Hs G.good := by
  have hM := trackMate_isMatching hends L G mk
  have hinc := (Finset.mem_filter.1 hF).2.2
  rw [StubGraph.inc] at hinc
  rcases Nat.eq_zero_or_pos ((trackGraph X L G mk).E.filter (fun e =>
      (trackGraph X L G mk).src e = F ∧ (trackGraph X L G mk).tgt e ∈
        (trackGraph X L G mk).Hs G.good)).card with h0 | h0
  · rw [h0, zero_add] at hinc
    obtain ⟨e, he⟩ := Finset.card_pos.1 hinc
    obtain ⟨heE, htgt, hsrc⟩ := Finset.mem_filter.1 he
    obtain ⟨q, hq, hm, hs, ht⟩ := StubGraph.ofHalfEdges_edge_mated (P := unmarkedPorts X L G mk)
      (v := Prod.fst) (mate := trackMate X) (mated := TrackMated X L G mk) heE
    have hs' : (trackGraph X L G mk).src e = q.1 := hs
    have ht' : (trackGraph X L G mk).tgt e = (trackMate X q).1 := ht
    obtain ⟨hmP, -, hinv, hmm⟩ := hM q hq hm
    refine ⟨trackMate X q, hmP, by rw [← ht', htgt], hmm, ?_⟩
    rw [hinv, ← hs']; exact hsrc
  · obtain ⟨e, he⟩ := Finset.card_pos.1 h0
    obtain ⟨heE, hsrc, htgt⟩ := Finset.mem_filter.1 he
    obtain ⟨q, hq, hm, hs, ht⟩ := StubGraph.ofHalfEdges_edge_mated (P := unmarkedPorts X L G mk)
      (v := Prod.fst) (mate := trackMate X) (mated := TrackMated X L G mk) heE
    have hs' : (trackGraph X L G mk).src e = q.1 := hs
    have ht' : (trackGraph X L G mk).tgt e = (trackMate X q).1 := ht
    exact ⟨q, hq, by rw [← hs', hsrc], hm, by rw [← ht']; exact htgt⟩

/-! ## Long sides of `J` and `H` faces -/

/-- **A `J` face has exactly one long side.** -/
theorem card_longSides_J :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X L G mk →
      ∀ F ∈ G.good, (trackGraph X L G mk).deg F = 3 → (longSides X L F).card = 1 := by
  filter_upwards [card_longSides, card_trackEnds] with n hcl hends hfm X hX htri L G mk hmk F hFg
    hdeg
  rw [trackGraph_deg (hends hfm X hX htri) L G mk hFg] at hdeg
  obtain ⟨hsub, hcard⟩ := hmk F hFg
  have hsd : (shortPorts X L F).card = 3 + G.marks F := by
    rw [← Finset.card_sdiff_add_card_eq_card hsub, hdeg, hcard]
  have hsep := hX.1.2
  have hFg' := hFg
  simp only [GoodFaces.good, Finset.mem_union] at hFg'
  rcases hFg' with (hp | hh) | ha
  · obtain ⟨hex, h5⟩ := G.pent_sub F hp
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hm : G.marks F = 1 := by simp [GoodFaces.marks, hp]
    omega
  · obtain ⟨hex, h6⟩ := G.hex_sub F hh
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hnp : F ∉ G.pent := fun hp => Finset.disjoint_left.1 G.disjoint_pent_hex hp hh
    have hm : G.marks F = 2 := by simp [GoodFaces.marks, hnp, hh]
    omega
  · obtain ⟨hex, h5⟩ := G.act_sub F ha
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hnp : F ∉ G.pent := fun hp => Finset.disjoint_left.1 G.disj hp ha
    have hnh : F ∉ G.hex := fun hh => Finset.disjoint_left.1 G.disjoint_hex_act hh ha
    have hm : G.marks F = 3 := by simp [GoodFaces.marks, hnp, hnh]
    omega

/-- **A degree-two face has no or two long sides.** -/
theorem card_longSides_H :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X L G mk →
      ∀ F ∈ G.good, (trackGraph X L G mk).deg F = 2 →
        (longSides X L F).card = 0 ∨ (longSides X L F).card = 2 := by
  filter_upwards [card_longSides, card_trackEnds] with n hcl hends hfm X hX htri L G mk hmk F hFg
    hdeg
  rw [trackGraph_deg (hends hfm X hX htri) L G mk hFg] at hdeg
  obtain ⟨hsub, hcard⟩ := hmk F hFg
  have hsd : (shortPorts X L F).card = 2 + G.marks F := by
    rw [← Finset.card_sdiff_add_card_eq_card hsub, hdeg, hcard]
  have hsep := hX.1.2
  have hFg' := hFg
  simp only [GoodFaces.good, Finset.mem_union] at hFg'
  rcases hFg' with (hp | hh) | ha
  · obtain ⟨hex, h5⟩ := G.pent_sub F hp
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hm : G.marks F = 1 := by simp [GoodFaces.marks, hp]
    omega
  · obtain ⟨hex, h6⟩ := G.hex_sub F hh
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hnp : F ∉ G.pent := fun hp => Finset.disjoint_left.1 G.disjoint_pent_hex hp hh
    have hm : G.marks F = 2 := by simp [GoodFaces.marks, hnp, hh]
    omega
  · obtain ⟨hex, h5⟩ := G.act_sub F ha
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hnp : F ∉ G.pent := fun hp => Finset.disjoint_left.1 G.disj hp ha
    have hnh : F ∉ G.hex := fun hh => Finset.disjoint_left.1 G.disjoint_hex_act hh ha
    have hm : G.marks F = 3 := by simp [GoodFaces.marks, hnp, hnh]
    omega

/-- **The margin of the long-side sums at a `J` neighbour and its `H` neighbour.** -/
lemma JH_margin {κ : ℝ} (hκ : 0 < κ) {τ : ℂ} (hτ : ‖τ‖ = 1) {A B : Finset (ℂ × ℂ)}
    (hA : A.card = 1) (hB : B.card = 0 ∨ B.card = 2)
    (hunit : ∀ ab ∈ A ∪ B, ‖ab.2 - ab.1‖ = 1)
    (hm : ∀ ab ∈ A ∪ B, ((ab.2 - ab.1) * conj τ).re ≤ 1 / 2 - κ) :
    min 1 κ ≤ ‖∑ ab ∈ A, (ab.2 - ab.1)‖ ∧
      min 1 κ ≤ ‖∑ ab ∈ A, (ab.2 - ab.1) + ∑ ab ∈ B, (ab.2 - ab.1)‖ := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hA
  have ha1 : ‖a.2 - a.1‖ = 1 := hunit a (by simp)
  rw [Finset.sum_singleton]
  refine ⟨by rw [ha1]; exact min_le_left _ _, ?_⟩
  rcases hB with hB | hB
  · rw [Finset.card_eq_zero.1 hB, Finset.sum_empty, add_zero, ha1]; exact min_le_left _ _
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hB
    rw [Finset.sum_pair hxy, ← add_assoc]
    exact three_unit_sum_lb hκ hτ ha1 (hunit x (by simp)) (hunit y (by simp)) (hm a (by simp))
      (hm x (by simp)) (hm y (by simp))

end Erdos99
end

end CaplessKGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessKElim`
-/

section CaplessKElim

/-!
# Eliminating the two-stage responses of a capless `K` component (Verification Guide §12.2)

At a capless component of `K` an outgoing port may end at a `J` face, whose response `p` is a root
of a quadratic whose coefficients involve the response `v` of one of its `H` neighbours, itself a
root of the response quadratic of that neighbour.  Eliminating `v` gives a quartic in `p`.

* `res22`: the resultant of two quadratics, with soundness (`res22_eq_zero_of_common_root`) and
  completeness (`exists_common_root_of_res22`);
* `jQuartic`: the quartic in `p` obtained by eliminating `v`;
* `qK b …`: the response polynomial of an outgoing port (the square of the `H` quadratic when
  `b = false`, the quartic when `b = true`), always of degree at most four;
* `elimPK`, `elimQK`: the iterated elimination over a sequence of quartics, with soundness,
  completeness and naturality.
-/

open Polynomial ComplexConjugate

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessKElim

open CaplessElim

/-! ## The resultant of two quadratics -/

/-- The resultant of `a₂ v² + a₁ v + a₀` and `b₂ v² + b₁ v + b₀`. -/
def res22 {R : Type*} [CommRing R] (a2 a1 a0 b2 b1 b0 : R) : R :=
  (a2 * b0 - a0 * b2) ^ 2 - (a2 * b1 - a1 * b2) * (a1 * b0 - a0 * b1)

lemma res22_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a2 a1 a0 b2 b1 b0 : R) :
    φ (res22 a2 a1 a0 b2 b1 b0) = res22 (φ a2) (φ a1) (φ a0) (φ b2) (φ b1) (φ b0) := by
  simp [res22]

/-- **Soundness**: a common root makes the resultant vanish. -/
lemma res22_eq_zero_of_common_root {a2 a1 a0 b2 b1 b0 v : ℂ}
    (hf : a2 * v ^ 2 + a1 * v + a0 = 0) (hg : b2 * v ^ 2 + b1 * v + b0 = 0) :
    res22 a2 a1 a0 b2 b1 b0 = 0 := by
  by_cases hv : v = 0
  · subst hv
    have h0 : a0 = 0 := by simpa using hf
    have h0' : b0 = 0 := by simpa using hg
    simp [res22, h0, h0']
  · have h1 : (a2 * b1 - a1 * b2) * v + (a2 * b0 - a0 * b2) = 0 := by
      linear_combination a2 * hg - b2 * hf
    have h2 : (a2 * b0 - a0 * b2) * v + (a1 * b0 - a0 * b1) = 0 := by
      have h3 : v * ((a2 * b0 - a0 * b2) * v + (a1 * b0 - a0 * b1)) = 0 := by
        linear_combination b0 * hf - a0 * hg
      exact (mul_eq_zero.1 h3).resolve_left hv
    unfold res22
    linear_combination (a2 * b0 - a0 * b2) * h1 - (a2 * b1 - a1 * b2) * h2

/-- **Completeness**: if the leading coefficient of the first quadratic does not vanish and the
resultant vanishes, there is a common root. -/
lemma exists_common_root_of_res22 {a2 a1 a0 b2 b1 b0 : ℂ} (ha : a2 ≠ 0)
    (h : res22 a2 a1 a0 b2 b1 b0 = 0) :
    ∃ v : ℂ, a2 * v ^ 2 + a1 * v + a0 = 0 ∧ b2 * v ^ 2 + b1 * v + b0 = 0 := by
  obtain ⟨v1, hv1⟩ := exists_quadratic_eq_zero (b := a1) (c := a0) ha (IsAlgClosed.exists_eq_mul_self _)
  set v2 := -a1 / a2 - v1 with hv2
  have e1 : a1 = -a2 * (v1 + v2) := by rw [hv2]; field_simp; ring
  have e0 : a0 = a2 * v1 * v2 := by
    have : a2 * v1 * v2 = -(a1 * v1) - a2 * v1 ^ 2 := by rw [hv2]; field_simp
    rw [this]; linear_combination hv1
  have hfac : res22 a2 a1 a0 b2 b1 b0 =
      a2 ^ 2 * (b2 * v1 ^ 2 + b1 * v1 + b0) * (b2 * v2 ^ 2 + b1 * v2 + b0) := by
    rw [res22, e1, e0]; ring
  rw [hfac] at h
  have hroot : ∀ v, v = v1 ∨ v = v2 → a2 * v ^ 2 + a1 * v + a0 = 0 := by
    rintro v (rfl | rfl) <;> rw [e1, e0] <;> ring
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) ha
    · exact ⟨v1, hroot v1 (Or.inl rfl), h⟩
  · exact ⟨v2, hroot v2 (Or.inr rfl), h⟩

/-! ## The quartic of a `J` response -/

variable {B : Type*} [CommRing B]

/-- The coefficient of `v²` in the `J` quadratic, as a polynomial in `p`. -/
def jB2 (l Zc : B) : B[X][X] := -C (respC l Zc) * X + C X

/-- The coefficient of `v` in the `J` quadratic. -/
def jB1 (l Z Zc : B) : B[X][X] :=
  C (respC l Zc) * X ^ 2 - C (X + respA l Z * respC l Zc) * X + C (X * respA l Z)

/-- The constant coefficient (in `v`) of the `J` quadratic. -/
def jB0 (l Z : B) : B[X][X] := C X * X ^ 2 - C (X * respA l Z) * X

/-- The quartic in `p` of a `J` response with data `(l, Z, Zc)` whose `H` neighbour has data
`(k, W, Wc)`: the resultant in `v` of the `H` quadratic and the `J` quadratic. -/
def jQuartic (l Z Zc k W Wc : B) : B[X][X] :=
  res22 (C (respC k Wc)) (C (-(respA k W * respC k Wc))) (C (X * respA k W))
    (jB2 l Zc) (jB1 l Z Zc) (jB0 l Z)

/-- The response polynomial of an outgoing port: the square of the `H` quadratic (`b = false`) or
the `J` quartic (`b = true`). -/
def qK (b : Bool) (k Z Zc k2 Z2 Zc2 : B) : B[X][X] :=
  if b then jQuartic k Z Zc k2 Z2 Zc2 else respQ k Z Zc ^ 2

section map

variable {B' : Type*} [CommRing B'] (φ : B →+* B')

lemma jQuartic_map (l Z Zc k W Wc : B) :
    (jQuartic l Z Zc k W Wc).map (mapRingHom φ) =
      jQuartic (φ l) (φ Z) (φ Zc) (φ k) (φ W) (φ Wc) := by
  simp [jQuartic, res22, jB2, jB1, jB0, respA, respC]
  ring

lemma qK_map (b : Bool) (k Z Zc k2 Z2 Zc2 : B) :
    (qK b k Z Zc k2 Z2 Zc2).map (mapRingHom φ) =
      qK b (φ k) (φ Z) (φ Zc) (φ k2) (φ Z2) (φ Zc2) := by
  cases b
  · simp only [qK, Bool.false_eq_true, if_false, Polynomial.map_pow, respQ_map]
  · simp only [qK, if_true, jQuartic_map]

end map

lemma natDegree_jQuartic_le (l Z Zc k W Wc : B) : (jQuartic l Z Zc k W Wc).natDegree ≤ 4 := by
  unfold jQuartic res22 jB2 jB1 jB0
  compute_degree

lemma natDegree_qK_le (b : Bool) (k Z Zc k2 Z2 Zc2 : B) : (qK b k Z Zc k2 Z2 Zc2).natDegree ≤ 4 := by
  cases b
  · simp only [qK, Bool.false_eq_true, if_false]
    exact natDegree_pow_le.trans (by have := natDegree_respQ_le k Z Zc; omega)
  · simp only [qK, if_true]; exact natDegree_jQuartic_le _ _ _ _ _ _

/-! ## The iterated elimination over quartics -/

/-- One elimination step: `Res_p (q(p), P(w + p))` with formal degrees `4` and `n`. -/
def elimStep4 (q : B[X][X]) (n : ℕ) (P : B[X][X]) : B[X][X] :=
  resultant (q.map C) (taylor (X : B[X][X]) (P.map C)) 4 n

/-- The iterated elimination: `elimPK 0 = w`, `elimPK (j+1) = Res_p (q_j(p), elimPK j (w + p))`. -/
def elimPK (q : ℕ → B[X][X]) : ℕ → B[X][X]
  | 0 => X
  | j + 1 => elimStep4 (q j) (4 ^ j) (elimPK q j)

/-- The eliminated polynomial in `T`: `elimPK m` at `w = k₀ T + Z₀`. -/
def elimQK (k0 Z0 : B) (q : ℕ → B[X][X]) (m : ℕ) : B[X] :=
  (elimPK q m).eval (respA k0 Z0)

lemma elimPK_congr {q q' : ℕ → B[X][X]} {j : ℕ} (h : ∀ i < j, q i = q' i) :
    elimPK q j = elimPK q' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [elimPK, elimPK, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h j (Nat.lt_succ_self j)]

lemma elimQK_congr {k0 Z0 : B} {q q' : ℕ → B[X][X]} {m : ℕ} (h : ∀ i < m, q i = q' i) :
    elimQK k0 Z0 q m = elimQK k0 Z0 q' m := by
  rw [elimQK, elimQK, elimPK_congr h]

section map

variable {B' : Type*} [CommRing B'] (φ : B →+* B')

lemma elimStep4_map (q : B[X][X]) (n : ℕ) (P : B[X][X]) :
    (elimStep4 q n P).map (mapRingHom φ) =
      elimStep4 (q.map (mapRingHom φ)) n (P.map (mapRingHom φ)) := by
  rw [elimStep4, elimStep4, ← coe_mapRingHom (f := mapRingHom φ), ← resultant_map_map]
  congr 1
  · rw [coe_mapRingHom, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext <;> simp
  · rw [coe_mapRingHom, map_taylor, Polynomial.map_map, Polynomial.map_map]
    simp only [coe_mapRingHom, map_X]
    congr 2
    ext <;> simp

lemma elimPK_map (q : ℕ → B[X][X]) (j : ℕ) :
    (elimPK q j).map (mapRingHom φ) = elimPK (fun i => (q i).map (mapRingHom φ)) j := by
  induction j with
  | zero => simp [elimPK]
  | succ j ih => rw [elimPK, elimPK, elimStep4_map, ih]

lemma elimQK_map (k0 Z0 : B) (q : ℕ → B[X][X]) (m : ℕ) :
    (elimQK k0 Z0 q m).map φ =
      elimQK (φ k0) (φ Z0) (fun i => (q i).map (mapRingHom φ)) m := by
  rw [elimQK, elimQK, ← elimPK_map φ, ← coe_mapRingHom, ← Polynomial.eval_map_apply]
  simp [respA]

end map

lemma natDegree_elimStep4_le (q : B[X][X]) {n : ℕ} {P : B[X][X]} (hP : P.natDegree ≤ n) :
    (elimStep4 q n P).natDegree ≤ 4 * n := by
  have h := natDegree_resultant_le (q.map C) (taylor (X : B[X][X]) (P.map C)) 4 n (a := 0) (b := n)
    (fun i => by rw [coeff_map, natDegree_C]) (fun i => by
      rw [coeff_taylor_map_C]; exact (natDegree_hasseDeriv_le _ _).trans (by omega))
  simpa [elimStep4] using h

lemma natDegree_elimPK_le (q : ℕ → B[X][X]) (j : ℕ) : (elimPK q j).natDegree ≤ 4 ^ j := by
  induction j with
  | zero => simp only [elimPK, pow_zero]; exact natDegree_X_le
  | succ j ih => rw [elimPK, pow_succ, mul_comm]; exact natDegree_elimStep4_le _ ih

lemma elimStep4_evTw (q P : ℂ[X][X]) (n : ℕ) (ζ w0 : ℂ) :
    evTw ζ w0 (elimStep4 q n P) =
      resultant (q.map (evalRingHom ζ)) (taylor w0 (P.map (evalRingHom ζ))) 4 n := by
  rw [elimStep4, ← resultant_map_map, Polynomial.map_map, evTw_C, map_taylor, evTw_X,
    Polynomial.map_map, evTw_C]

/-- **Soundness of the elimination.** -/
theorem elimPK_eval_eq_zero (q : ℕ → ℂ[X][X]) (hq : ∀ i, (q i).natDegree ≤ 4) (ζ : ℂ)
    (p : ℕ → ℂ) (j : ℕ) (hp : ∀ i < j, ((q i).map (evalRingHom ζ)).eval (p i) = 0)
    (w0 : ℂ) (hw : w0 + ∑ i ∈ Finset.range j, p i = 0) :
    ((elimPK q j).eval (C w0)).eval ζ = 0 := by
  induction j generalizing w0 with
  | zero => simpa [elimPK] using hw
  | succ j ih =>
    rw [← evTw_apply, elimPK, elimStep4_evTw]
    set f := (q j).map (evalRingHom ζ)
    set g := taylor w0 ((elimPK q j).map (evalRingHom ζ))
    have hf : f.natDegree ≤ 4 := natDegree_map_le.trans (hq j)
    have hg : g.natDegree ≤ 4 ^ j := by
      rw [natDegree_taylor]; exact natDegree_map_le.trans (natDegree_elimPK_le _ _)
    obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg (Or.inl four_ne_zero)
    have h1 : f.eval (p j) = 0 := hp j (Nat.lt_succ_self j)
    have h2 : g.eval (p j) = 0 := by
      simp only [g, taylor_eval, eval_map_evalRingHom]
      refine ih (fun i hi => hp i (Nat.lt_succ_of_lt hi)) _ ?_
      rw [Finset.sum_range_succ] at hw
      linear_combination hw
    have := congrArg (eval (p j)) hab
    simp only [eval_add, eval_mul, h1, h2, zero_mul, add_zero, eval_C] at this
    exact this.symm

/-- **Completeness of the elimination**: if `elimPK j` vanishes at `(ζ, w₀)` and the quartic
coefficients of the `q_i(ζ)` (`i < j`) do not vanish, there are roots `p_i` with
`w₀ + Σ_{i<j} p_i = 0`. -/
theorem exists_roots_of_elimPK_eval (q : ℕ → ℂ[X][X]) (hq : ∀ i, (q i).natDegree ≤ 4) (ζ : ℂ)
    (j : ℕ) (hlc : ∀ i < j, ((q i).map (evalRingHom ζ)).coeff 4 ≠ 0) (w0 : ℂ)
    (h : ((elimPK q j).eval (C w0)).eval ζ = 0) :
    ∃ p : ℕ → ℂ, (∀ i < j, ((q i).map (evalRingHom ζ)).eval (p i) = 0) ∧
      w0 + ∑ i ∈ Finset.range j, p i = 0 := by
  induction j generalizing w0 with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), by simpa [elimPK] using h⟩
  | succ j ih =>
    rw [← evTw_apply, elimPK, elimStep4_evTw] at h
    set f := (q j).map (evalRingHom ζ) with hfdef
    set g := taylor w0 ((elimPK q j).map (evalRingHom ζ))
    have hc4 : f.coeff 4 ≠ 0 := hlc j (Nat.lt_succ_self j)
    have hfdeg : f.natDegree = 4 :=
      le_antisymm (natDegree_map_le.trans (hq j)) (le_natDegree_of_ne_zero hc4)
    have hg : g.natDegree ≤ 4 ^ j := by
      rw [natDegree_taylor]; exact natDegree_map_le.trans (natDegree_elimPK_le _ _)
    have hres := resultant_eq_prod_eval f g (4 ^ j) hg (IsAlgClosed.splits f)
    rw [hfdeg, h] at hres
    have hlc0 : f.leadingCoeff ≠ 0 := by rw [leadingCoeff, hfdeg]; exact hc4
    have hprod : (f.roots.map g.eval).prod = 0 := by
      rcases mul_eq_zero.1 hres.symm with h0 | h0
      · exact absurd (pow_eq_zero_iff (by positivity) |>.1 h0) hlc0
      · exact h0
    obtain ⟨y, hy, hgy⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 hprod)
    have hf0 : f ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hfdeg; exact four_ne_zero hfdeg.symm
    have hfy : f.eval y = 0 := (mem_roots hf0).1 hy
    have hgy' : ((elimPK q j).eval (C (w0 + y))).eval ζ = 0 := by
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

/-! ## Evaluations over `ℂ` -/

/-- The `H` quadratic at `T`, as a function of `v`. -/
def hQuad (k W T v : ℂ) : ℂ :=
  (k + T * conj W) * v ^ 2 - (k * T + W) * (k + T * conj W) * v + T * (k * T + W)

/-- The `J` quadratic at `T`, as a function of `p` and of the `H` response `v`. -/
def jQuad (l Z T v p : ℂ) : ℂ :=
  ((l + T * conj Z) * v + T) * p ^ 2 - (l * T + Z + v) * ((l + T * conj Z) * v + T) * p +
    T * v * (l * T + Z + v)

lemma respQ_eval_hQuad (k W T v : ℂ) :
    ((respQ k W (conj W)).map (evalRingHom T)).eval v = hQuad k W T v := by
  rw [respQ_map_eval, hQuad]

lemma jQuartic_eval (l Z k W T p : ℂ) :
    ((jQuartic l Z (conj Z) k W (conj W)).map (evalRingHom T)).eval p =
      res22 (k + T * conj W) (-((k * T + W) * (k + T * conj W))) (T * (k * T + W))
        (-(l + T * conj Z) * p + T)
        ((l + T * conj Z) * p ^ 2 - (T + (l * T + Z) * (l + T * conj Z)) * p + T * (l * T + Z))
        (T * p ^ 2 - T * (l * T + Z) * p) := by
  simp [jQuartic, res22, jB2, jB1, jB0, respA, respC]
  ring

/-- The `J` quadratic, sorted by powers of `v`. -/
lemma jQuad_eq (l Z T v p : ℂ) :
    jQuad l Z T v p = (-(l + T * conj Z) * p + T) * v ^ 2 +
      ((l + T * conj Z) * p ^ 2 - (T + (l * T + Z) * (l + T * conj Z)) * p + T * (l * T + Z)) * v +
      (T * p ^ 2 - T * (l * T + Z) * p) := by
  unfold jQuad; ring

/-- **Soundness of the quartic**: a `J` response over an `H` response is a root of the quartic. -/
lemma jQuartic_eval_eq_zero {l Z k W T v p : ℂ} (hv : hQuad k W T v = 0) (hp : jQuad l Z T v p = 0) :
    ((jQuartic l Z (conj Z) k W (conj W)).map (evalRingHom T)).eval p = 0 := by
  rw [jQuartic_eval]
  refine res22_eq_zero_of_common_root (v := v) ?_ ?_
  · rw [hQuad] at hv; linear_combination hv
  · rw [jQuad_eq] at hp; linear_combination hp

/-- **Completeness of the quartic**. -/
lemma exists_of_jQuartic_eval {l Z k W T p : ℂ} (ha : k + T * conj W ≠ 0)
    (h : ((jQuartic l Z (conj Z) k W (conj W)).map (evalRingHom T)).eval p = 0) :
    ∃ v, hQuad k W T v = 0 ∧ jQuad l Z T v p = 0 := by
  rw [jQuartic_eval] at h
  obtain ⟨v, h1, h2⟩ := exists_common_root_of_res22 ha h
  refine ⟨v, ?_, ?_⟩
  · rw [hQuad]; linear_combination h1
  · rw [jQuad_eq]; linear_combination h2

/-! ## Quartic coefficients -/

lemma coeff_mul_top {p q : ℂ[X]} {m n : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  rw [coeff_mul, Finset.sum_eq_single (m, n)]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    by_cases hi : m < i
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    · have hj : n < j := by
        by_contra hj
        exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
      rw [coeff_eq_zero_of_natDegree_lt (p := q) (by omega), mul_zero]
  · intro h; simp at h

lemma coeff_two_aux (a b c : ℂ) : (C a * X ^ 2 + C b * X + C c).coeff 2 = a := by
  simp

lemma natDegree_two_aux (a b c : ℂ) : (C a * X ^ 2 + C b * X + C c).natDegree ≤ 2 := by
  compute_degree

lemma respQ_map_eq (k W T : ℂ) : (respQ k W (conj W)).map (evalRingHom T) =
    C (k + T * conj W) * X ^ 2 + C (-((k * T + W) * (k + T * conj W))) * X +
      C (T * (k * T + W)) := by
  simp only [respQ, respA, respC, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, map_C, map_X, coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X]
  simp only [map_add, map_mul, map_neg]
  ring

lemma coeff_four_sq_respQ (k W T : ℂ) :
    ((respQ k W (conj W) ^ 2).map (evalRingHom T)).coeff 4 = (k + T * conj W) ^ 2 := by
  rw [Polynomial.map_pow, respQ_map_eq, show (4 : ℕ) = 2 * 2 from rfl,
    coeff_pow_of_natDegree_le (natDegree_two_aux _ _ _), coeff_two_aux]

lemma jQuartic_map_eq (l Z k W T : ℂ) :
    (jQuartic l Z (conj Z) k W (conj W)).map (evalRingHom T) =
      (C ((k + T * conj W) * T) * X ^ 2 +
        C (T * (k * T + W) * (l + T * conj Z) - (k + T * conj W) * T * (l * T + Z)) * X +
        C (-(T * (k * T + W) * T))) ^ 2 -
      (C ((k + T * conj W) * (l + T * conj Z)) * X ^ 2 +
        C (-((k + T * conj W) * (T + (l * T + Z) * (l + T * conj Z))) -
          (k * T + W) * (k + T * conj W) * (l + T * conj Z)) * X +
        C ((k + T * conj W) * T * (l * T + Z) + (k * T + W) * (k + T * conj W) * T)) *
      (C (-((k * T + W) * (k + T * conj W)) * T - T * (k * T + W) * (l + T * conj Z)) * X ^ 2 +
        C ((k * T + W) * (k + T * conj W) * T * (l * T + Z) +
          T * (k * T + W) * (T + (l * T + Z) * (l + T * conj Z))) * X +
        C (-(T * (k * T + W) * T * (l * T + Z)))) := by
  simp only [jQuartic, res22, jB2, jB1, jB0, respA, respC, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_neg, map_C, map_X, coe_evalRingHom,
    eval_add, eval_mul, eval_C, eval_X, eval_neg]
  simp only [map_add, map_mul, map_neg, map_sub]
  ring

/-- The quartic coefficient of the `J` quartic at `T`. -/
lemma coeff_four_jQuartic (l Z k W T : ℂ) :
    ((jQuartic l Z (conj Z) k W (conj W)).map (evalRingHom T)).coeff 4 =
      (k + T * conj W) * ((k + T * conj W) * T ^ 2 +
        (k * T + W) * (k + T * conj W) * (l + T * conj Z) * T +
        T * (k * T + W) * (l + T * conj Z) ^ 2) := by
  rw [jQuartic_map_eq, coeff_sub, show (4 : ℕ) = 2 * 2 from rfl,
    coeff_pow_of_natDegree_le (natDegree_two_aux _ _ _),
    show (2 * 2 : ℕ) = 2 + 2 from rfl,
    coeff_mul_top (natDegree_two_aux _ _ _) (natDegree_two_aux _ _ _),
    coeff_two_aux, coeff_two_aux, coeff_two_aux]
  ring

end CaplessKElim

end Erdos99
end

end CaplessKElim

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessKPoly`
-/

section CaplessKPoly

/-!
# The `K`-component polynomial is not zero (Verification Guide §12.3, §13.4)

Along a real parameter `T → ∞`:

* `hRoot_facts`: a root `v` of the `H` quadratic is nonzero, `v / T` is bounded with real part
  `≥ -ε`, and `1 / v` is close to `0` or to `conj W`;
* `jRoot_facts`: if `Z ≠ 0` and `Z + W ≠ 0`, every `J` response `p` over such a `v` has
  `Re (p / T) ≥ -ε`, and the leading coefficient of the `J` quadratic does not vanish;
* `qK_root_facts`: the quartic coefficient of `qK` is eventually nonzero and all its roots have
  `Re (p / T) ≥ -ε`;
* `elimQK_ne_zero_of`: the abstract nonvanishing argument: if `k₀ > 0` and all roots of the
  response polynomials have asymptotically nonnegative real part, the eliminated polynomial is not
  zero.
-/

open Polynomial Filter ComplexConjugate

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessKElim

open CaplessElim

/-- If `x (x - A) = δ` with `‖δ‖ ≤ η²`, then `x` is `η`-close to `0` or to `A`. -/
lemma near_zero_or_near {x A δ : ℂ} {η : ℝ} (hη : 0 ≤ η) (h : x * (x - A) = δ)
    (hδ : ‖δ‖ ≤ η ^ 2) : ‖x‖ ≤ η ∨ ‖x - A‖ ≤ η := by
  by_contra hcon
  push_neg at hcon
  have := mul_lt_mul'' hcon.1 hcon.2 hη hη
  rw [← norm_mul, h] at this
  nlinarith

lemma k_facts {k : ℝ} (hk : k = 1 ∨ k = 2) : 1 ≤ k ∧ k ≤ 2 := by
  rcases hk with rfl | rfl <;> norm_num

/-- The leading coefficient `k + T conj W` of the `H` quadratic is eventually nonzero. -/
lemma respC_eventually_ne {k : ℝ} (hk : k = 1 ∨ k = 2) (W : ℂ) :
    ∀ᶠ T : ℝ in atTop, (k : ℂ) + T * conj W ≠ 0 := by
  obtain ⟨hk1, hk2⟩ := k_facts hk
  by_cases hW : W = 0
  · refine Eventually.of_forall fun T => ?_
    rw [hW, map_zero, mul_zero, add_zero]
    exact_mod_cast (by linarith : k ≠ 0)
  · have hWn : 0 < ‖W‖ := norm_pos_iff.2 hW
    filter_upwards [eventually_gt_atTop (3 / ‖W‖)] with T hT h0
    have hT0 : 0 < T := lt_trans (by positivity) hT
    have h1 : (T : ℂ) * conj W = -(k : ℂ) := by linear_combination h0
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hT0.le, norm_neg,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h2
    have h3 : 3 < T * ‖W‖ := by rwa [div_lt_iff₀ hWn] at hT
    linarith

lemma re_ge_neg_norm (x : ℂ) : -‖x‖ ≤ x.re := by
  have := Complex.abs_re_le_norm x
  linarith [neg_abs_le x.re]

/-- Roots of `x² - k x + 1` (`0 < k ≤ 2`) have positive real part and norm at most `3`. -/
lemma zeroW_root {k : ℝ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) {x : ℂ} (hx : x ^ 2 - k * x + 1 = 0) :
    0 ≤ x.re ∧ ‖x‖ ≤ 3 := by
  constructor
  · have hre := congrArg Complex.re hx
    have him := congrArg Complex.im hx
    simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.one_im, Complex.zero_im] at hre him
    by_cases ht : x.im = 0
    · rw [ht] at hre; nlinarith
    · have : 2 * x.re = k := by
        have h' : x.im * (2 * x.re - k) = 0 := by linarith
        have := (mul_eq_zero.1 h').resolve_left ht
        linarith
      linarith
  · by_contra hcon
    push_neg at hcon
    have h1 : x ^ 2 = k * x - 1 := by linear_combination hx
    have h2 := congrArg norm h1
    rw [norm_pow] at h2
    have h3 : ‖(k : ℂ) * x - 1‖ ≤ k * ‖x‖ + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_one]
    nlinarith

/-- **Roots of the `H` quadratic.** -/
theorem hRoot_facts {k : ℝ} (hk : k = 1 ∨ k = 2) (W : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℂ, hQuad k W T v = 0 →
      v ≠ 0 ∧ ‖v / T‖ ≤ 3 ∧ -ε ≤ (v / T).re ∧ (‖v⁻¹‖ ≤ ε ∨ ‖v⁻¹ - conj W‖ ≤ ε) := by
  obtain ⟨hk1, hk2⟩ := k_facts hk
  set η : ℝ := min ε (1 / 2) with hη
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hη2 : η ≤ 1 / 2 := min_le_right _ _
  filter_upwards [eventually_ge_atTop (2 * ‖W‖ + 1), eventually_ge_atTop (8 * (2 + ‖W‖) / ε ^ 2),
    eventually_ge_atTop (4 / ε), eventually_ge_atTop (6 / (‖W‖ * η ^ 2)),
    eventually_ge_atTop (4 / ‖W‖)] with T hT1 hT2 hT3 hT4 hT5 v hv
  have hW0 : 0 ≤ ‖W‖ := norm_nonneg _
  have hT0 : 0 < T := by linarith
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  set a : ℂ := k * T + W with ha
  set as : ℂ := k / T + conj W with has
  have hq : as * v ^ 2 - a * as * v + a = 0 := by
    have : (T : ℂ) * (as * v ^ 2 - a * as * v + a) = 0 := by
      rw [← hv, hQuad, has, ha]; field_simp
    exact (mul_eq_zero.1 this).resolve_left hTc
  clear_value a as
  have hkT : ‖(k : ℂ) / T‖ = k / T := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg hT0.le]
  have hkT2 : k / T ≤ 2 / T := div_le_div_of_nonneg_right hk2 hT0.le
  -- `a` is large
  have hanorm : T / 2 ≤ ‖a‖ := by
    have h1 : ‖(k : ℂ) * T‖ = k * T := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
        Real.norm_of_nonneg hT0.le]
    have h2 := norm_sub_norm_le ((k : ℂ) * T) (-W)
    rw [sub_neg_eq_add, norm_neg, h1, ← ha] at h2
    nlinarith
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at hanorm; linarith
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hq
    exact ha0 hq
  have hasnorm : ‖as‖ ≤ 2 + ‖W‖ := by
    rw [has]
    refine (norm_add_le _ _).trans ?_
    rw [hkT, Complex.norm_conj]
    have : 2 / T ≤ 2 := by rw [div_le_iff₀ hT0]; linarith
    linarith
  refine ⟨hv0, ?_⟩
  -- the reciprocal
  have hyeq : v⁻¹ * (v⁻¹ - as) = -(as / a) := by
    have e : v⁻¹ * (v⁻¹ - as) + as / a = (as * v ^ 2 - a * as * v + a) / (a * v ^ 2) := by
      field_simp; ring
    rw [hq, zero_div] at e
    linear_combination e
  have hδ1 : ‖-(as / a)‖ ≤ (ε / 2) ^ 2 := by
    rw [norm_neg, norm_div]
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
    rw [div_le_iff₀ hapos]
    have h8 : 8 * (2 + ‖W‖) ≤ T * ε ^ 2 := by rwa [div_le_iff₀ (by positivity)] at hT2
    nlinarith
  have hy : ‖v⁻¹‖ ≤ ε ∨ ‖v⁻¹ - conj W‖ ≤ ε := by
    rcases near_zero_or_near (by positivity) hyeq hδ1 with h | h
    · left; linarith
    · right
      have h4 : 2 / T ≤ ε / 2 := by
        rw [div_le_iff₀ hT0]; rw [div_le_iff₀ hε] at hT3; linarith
      calc ‖v⁻¹ - conj W‖ = ‖(v⁻¹ - as) + (k : ℂ) / T‖ := by rw [has]; ring_nf
        _ ≤ ‖v⁻¹ - as‖ + ‖(k : ℂ) / T‖ := norm_add_le _ _
        _ ≤ ε := by rw [hkT]; linarith
  -- the normalised response
  by_cases hW : W = 0
  · have hx : (v / T) ^ 2 - k * (v / T) + 1 = 0 := by
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by linarith : k ≠ 0)
      have e : (v / T) ^ 2 - k * (v / T) + 1 = (as * v ^ 2 - a * as * v + a) / (k * T) := by
        rw [ha, has, hW, map_zero, add_zero, add_zero]; field_simp
      rw [e, hq, zero_div]
    obtain ⟨h1, h2⟩ := zeroW_root hk1 hk2 hx
    exact ⟨h2, by linarith, hy⟩
  · have hWn : 0 < ‖W‖ := norm_pos_iff.2 hW
    have has_lb : ‖W‖ / 2 ≤ ‖as‖ := by
      have h1 := norm_sub_norm_le (conj W) (-((k : ℂ) / T))
      rw [sub_neg_eq_add, norm_neg, hkT, Complex.norm_conj, add_comm, ← has] at h1
      have : 2 / T ≤ ‖W‖ / 2 := by
        rw [div_le_iff₀ hT0]; rw [div_le_iff₀ hWn] at hT5; linarith
      linarith
    have has0 : as ≠ 0 := fun h => by rw [h, norm_zero] at has_lb; linarith
    have hxeq : (v / T) * (v / T - a / T) = -(a / (T ^ 2 * as)) := by
      have e : (v / T) * (v / T - a / T) + a / (T ^ 2 * as) =
          (as * v ^ 2 - a * as * v + a) / (T ^ 2 * as) := by
        field_simp
      rw [hq, zero_div] at e
      linear_combination e
    have haT : ‖a / T‖ ≤ 5 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le, div_le_iff₀ hT0, ha]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
        Real.norm_of_nonneg hT0.le]
      nlinarith
    have hδ : ‖-(a / (T ^ 2 * as))‖ ≤ η ^ 2 := by
      rw [norm_neg, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hT0.le]
      have h1 : ‖a‖ ≤ 5 / 2 * T := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le, div_le_iff₀ hT0] at haT
        linarith
      have h6 : 6 ≤ T * (‖W‖ * η ^ 2) := by rwa [div_le_iff₀ (by positivity)] at hT4
      rw [div_le_iff₀ (by positivity)]
      have : T ^ 2 * (‖W‖ / 2) ≤ T ^ 2 * ‖as‖ := mul_le_mul_of_nonneg_left has_lb (by positivity)
      nlinarith
    have hreaT : 1 / 2 ≤ (a / T).re := by
      have : a / T = k + W / T := by rw [ha]; field_simp
      rw [this, Complex.add_re, Complex.ofReal_re]
      have h1 := re_ge_neg_norm (W / T)
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le] at h1
      have h2 : ‖W‖ / T ≤ 1 / 2 := by rw [div_le_iff₀ hT0]; linarith
      linarith
    rcases near_zero_or_near hη0.le hxeq hδ with h | h
    · exact ⟨by linarith, by linarith [re_ge_neg_norm (v / T)], hy⟩
    · refine ⟨?_, ?_, hy⟩
      · calc ‖v / T‖ = ‖(v / T - a / T) + a / T‖ := by ring_nf
          _ ≤ ‖v / T - a / T‖ + ‖a / T‖ := norm_add_le _ _
          _ ≤ 3 := by linarith
      · have h1 := re_ge_neg_norm (v / T - a / T)
        rw [Complex.sub_re] at h1
        linarith

/-- **`J` responses over an `H` response.** -/
theorem jRoot_facts {l k : ℝ} (hl : l = 1 ∨ l = 2) (hk : k = 1 ∨ k = 2) {Z W : ℂ} (hZ : Z ≠ 0)
    (hZW : Z + W ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℂ, hQuad k W T v = 0 →
      ((l : ℂ) + T * conj Z) * v + T ≠ 0 ∧ ∀ p : ℂ, jQuad l Z T v p = 0 → -ε ≤ (p / T).re := by
  obtain ⟨hl1, hl2⟩ := k_facts hl
  set c : ℝ := min ‖Z‖ ‖Z + W‖ with hc
  have hc0 : 0 < c := lt_min (norm_pos_iff.2 hZ) (norm_pos_iff.2 hZW)
  have hcZ : c ≤ ‖Z‖ := min_le_left _ _
  have hcZW : c ≤ ‖Z + W‖ := min_le_right _ _
  set ε' : ℝ := min (c / 4) (1 / 4) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hε'c : ε' ≤ c / 4 := min_le_left _ _
  have hε'1 : ε' ≤ 1 / 4 := min_le_right _ _
  set η : ℝ := min ε (1 / 4) with hη
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hη1 : η ≤ 1 / 4 := min_le_right _ _
  filter_upwards [hRoot_facts hk W hε'0, eventually_ge_atTop (8 / c),
    eventually_ge_atTop (4 * ‖Z‖ + 1), eventually_ge_atTop (12 / (c * η ^ 2))] with
    T hH hT1 hT2 hT3 v hv
  obtain ⟨hv0, hvT, hvre, hy⟩ := hH v hv
  have hZ0 : 0 ≤ ‖Z‖ := norm_nonneg _
  have hT0 : 0 < T := by linarith
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  set aJs : ℂ := l / T + conj Z + v⁻¹ with haJs
  set aJ : ℂ := l * T + Z + v with haJ
  have hlT : ‖(l : ℂ) / T‖ ≤ c / 4 := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg hT0.le, div_le_iff₀ hT0]
    rw [div_le_iff₀ hc0] at hT1
    linarith
  have hmid : 3 * c / 4 ≤ ‖conj Z + v⁻¹‖ := by
    rcases hy with h | h
    · have := norm_sub_norm_le (conj Z) (-v⁻¹)
      rw [sub_neg_eq_add, norm_neg, Complex.norm_conj] at this
      linarith
    · have e : conj Z + v⁻¹ = conj (Z + W) + (v⁻¹ - conj W) := by rw [map_add]; ring
      have := norm_sub_norm_le (conj (Z + W)) (-(v⁻¹ - conj W))
      rw [sub_neg_eq_add, norm_neg, Complex.norm_conj, ← e] at this
      linarith
  have haJs_lb : c / 2 ≤ ‖aJs‖ := by
    have := norm_sub_norm_le (conj Z + v⁻¹) (-((l : ℂ) / T))
    rw [sub_neg_eq_add, norm_neg] at this
    have e : conj Z + v⁻¹ + (l : ℂ) / T = aJs := by rw [haJs]; ring
    rw [e] at this
    linarith
  have haJs0 : aJs ≠ 0 := fun h => by rw [h, norm_zero] at haJs_lb; linarith
  have hcJ : ((l : ℂ) + T * conj Z) * v + T = T * v * aJs := by
    rw [haJs]; field_simp
  refine ⟨by rw [hcJ]; exact mul_ne_zero (mul_ne_zero hTc hv0) haJs0, fun p hp => ?_⟩
  have hp' : aJs * p ^ 2 - aJ * aJs * p + aJ = 0 := by
    have e : jQuad l Z T v p = T * v * (aJs * p ^ 2 - aJ * aJs * p + aJ) := by
      rw [jQuad, hcJ, haJ]; ring
    rw [e] at hp
    exact (mul_eq_zero.1 hp).resolve_left (mul_ne_zero hTc hv0)
  clear_value aJs aJ
  have hxeq : (p / T) * (p / T - aJ / T) = -(aJ / (T ^ 2 * aJs)) := by
    have e : (p / T) * (p / T - aJ / T) + aJ / (T ^ 2 * aJs) =
        (aJs * p ^ 2 - aJ * aJs * p + aJ) / (T ^ 2 * aJs) := by
      field_simp
    rw [hp', zero_div] at e
    linear_combination e
  have hZT : ‖Z / T‖ ≤ 1 / 4 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le, div_le_iff₀ hT0]; linarith
  have hlT' : ‖(l : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hl2
  have haJT_eq : aJ / T = l + Z / T + v / T := by rw [haJ]; field_simp
  have haJT : ‖aJ / T‖ ≤ 6 := by
    rw [haJT_eq]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (l : ℂ) (Z / T)
    linarith
  have hδ : ‖-(aJ / (T ^ 2 * aJs))‖ ≤ η ^ 2 := by
    have e : aJ / (T ^ 2 * aJs) = (aJ / T) / (T * aJs) := by field_simp
    rw [norm_neg, e, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hT0.le]
    have h12 : 12 ≤ T * (c * η ^ 2) := by rwa [div_le_iff₀ (by positivity)] at hT3
    rw [div_le_iff₀ (by positivity)]
    have : T * (c / 2) ≤ T * ‖aJs‖ := mul_le_mul_of_nonneg_left haJs_lb hT0.le
    nlinarith
  have hreaJ : 1 / 2 ≤ (aJ / T).re := by
    rw [haJT_eq, Complex.add_re, Complex.add_re, Complex.ofReal_re]
    have := re_ge_neg_norm (Z / T)
    linarith
  rcases near_zero_or_near hη0.le hxeq hδ with h | h
  · linarith [re_ge_neg_norm (p / T)]
  · have h1 := re_ge_neg_norm (p / T - aJ / T)
    rw [Complex.sub_re] at h1
    linarith

/-- Admissible data of one response: an `H` response (`b = false`) needs `k ∈ {1, 2}`; a `J`
response (`b = true`) also needs `k₂ ∈ {1, 2}`, `Z ≠ 0` and `Z + W ≠ 0`. -/
def RespAdm (b : Bool) (k : ℝ) (Z : ℂ) (k2 : ℝ) (W : ℂ) : Prop :=
  (k = 1 ∨ k = 2) ∧ (b = true → (k2 = 1 ∨ k2 = 2) ∧ Z ≠ 0 ∧ Z + W ≠ 0)

/-- **The response polynomial of one port**: eventually its quartic coefficient does not vanish
and all its roots have `Re (p / T) ≥ -ε`. -/
theorem qK_root_facts {b : Bool} {k : ℝ} {Z : ℂ} {k2 : ℝ} {W : ℂ} (h : RespAdm b k Z k2 W)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      ((qK b (k : ℂ) Z (conj Z) (k2 : ℂ) W (conj W)).map (evalRingHom (T : ℂ))).coeff 4 ≠ 0 ∧
      ∀ p : ℂ, ((qK b (k : ℂ) Z (conj Z) (k2 : ℂ) W (conj W)).map (evalRingHom (T : ℂ))).eval p = 0 →
        -ε ≤ (p / T).re := by
  obtain ⟨hk, hJ⟩ := h
  cases b
  · filter_upwards [respC_eventually_ne hk Z, hRoot_facts hk Z hε] with T hc hroot
    simp only [qK, Bool.false_eq_true, if_false]
    refine ⟨by rw [coeff_four_sq_respQ]; exact pow_ne_zero 2 hc, fun p hp => ?_⟩
    rw [Polynomial.map_pow, eval_pow, respQ_eval_hQuad] at hp
    exact (hroot p (pow_eq_zero_iff two_ne_zero |>.1 hp)).2.2.1
  · obtain ⟨hk2, hZ, hZW⟩ := hJ rfl
    filter_upwards [respC_eventually_ne hk2 W, jRoot_facts hk hk2 hZ hZW hε,
      eventually_gt_atTop 0] with T hc hroot hT0
    simp only [qK, if_true]
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    refine ⟨?_, fun p hp => ?_⟩
    · rw [coeff_four_jQuartic]
      refine mul_ne_zero hc ?_
      by_cases hα : (k : ℂ) + T * conj Z = 0
      · rw [hα]; simpa using mul_ne_zero hc (pow_ne_zero 2 hTc)
      · intro h0
        have hv : hQuad k2 W T (-T / ((k : ℂ) + T * conj Z)) = 0 := by
          have e : ((k : ℂ) + T * conj Z) ^ 2 * hQuad k2 W T (-T / ((k : ℂ) + T * conj Z)) =
              ((k2 : ℂ) + T * conj W) * T ^ 2 +
                ((k2 : ℂ) * T + W) * ((k2 : ℂ) + T * conj W) * ((k : ℂ) + T * conj Z) * T +
                T * ((k2 : ℂ) * T + W) * ((k : ℂ) + T * conj Z) ^ 2 := by
            rw [hQuad]; field_simp; ring
          rw [h0] at e
          exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero 2 hα)
        apply (hroot _ hv).1
        field_simp
        ring
    · obtain ⟨v, hv, hjv⟩ := exists_of_jQuartic_eval hc hp
      exact (hroot v hv).2 p hjv

/-- **The abstract nonvanishing argument** (Verification Guide §12.3): if `k₀ > 0` and, for every
`ε > 0`, eventually the quartic coefficients of the response polynomials do not vanish and all
their roots have `Re (p / T) ≥ -ε`, then the eliminated polynomial is not zero. -/
theorem elimQK_ne_zero_of {k0 : ℝ} (hk0 : 0 < k0) (Z0 : ℂ) (q : ℕ → ℂ[X][X])
    (hq : ∀ i, (q i).natDegree ≤ 4) (m : ℕ)
    (hroot : ∀ i < m, ∀ ε > 0, ∀ᶠ T : ℝ in atTop, ((q i).map (evalRingHom (T : ℂ))).coeff 4 ≠ 0 ∧
      ∀ p : ℂ, ((q i).map (evalRingHom (T : ℂ))).eval p = 0 → -ε ≤ (p / T).re) :
    elimQK (k0 : ℂ) Z0 q m ≠ 0 := by
  intro hQ
  set ε : ℝ := k0 / (2 * (m + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hall : ∀ᶠ T : ℝ in atTop, ∀ i ∈ Finset.range m,
      ((q i).map (evalRingHom (T : ℂ))).coeff 4 ≠ 0 ∧
      ∀ p : ℂ, ((q i).map (evalRingHom (T : ℂ))).eval p = 0 → -ε ≤ (p / T).re :=
    (Finset.eventually_all _).2 fun i hi => hroot i (Finset.mem_range.1 hi) ε hε
  obtain ⟨T, hT, hT0, hTb⟩ := (hall.and ((eventually_gt_atTop 0).and
    (eventually_gt_atTop (2 * ‖Z0‖ / k0 + 1)))).exists
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have h0 : ((elimPK q m).eval (C ((respA (k0 : ℂ) Z0).eval (T : ℂ)))).eval (T : ℂ) = 0 := by
    rw [← eval_eval_eq_eval_map]
    have : (elimQK (k0 : ℂ) Z0 q m).eval (T : ℂ) = 0 := by rw [hQ, eval_zero]
    exact this
  obtain ⟨p, hp, hs⟩ := exists_roots_of_elimPK_eval q hq _ m
    (fun i hi => (hT i (Finset.mem_range.2 hi)).1) _ h0
  have hs' : (k0 : ℂ) * T + Z0 + ∑ i ∈ Finset.range m, p i = 0 := by simpa [respA] using hs
  have hsum : (k0 : ℂ) + Z0 / T + ∑ i ∈ Finset.range m, p i / T = 0 := by
    rw [← Finset.sum_div]
    field_simp
    linear_combination hs'
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.add_re, Complex.re_sum, Complex.ofReal_re, Complex.zero_re] at hre
  have h1 : -(‖Z0‖ / T) ≤ (Z0 / T).re := by
    have := re_ge_neg_norm (Z0 / T)
    rwa [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le] at this
  have h2 : ∀ i ∈ Finset.range m, -ε ≤ (p i / T).re := fun i hi =>
    (hT i hi).2 (p i) (hp i (Finset.mem_range.1 hi))
  have h5 : -(m * ε) ≤ ∑ i ∈ Finset.range m, (p i / T).re := by
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

/-- The response polynomials of a `K` component with port types `b`. -/
def kq (b : ℕ → Bool) (k : ℕ → ℝ) (Z : ℕ → ℂ) (k2 : ℕ → ℝ) (W : ℕ → ℂ) : ℕ → ℂ[X][X] :=
  fun i => qK (b i) (k i : ℂ) (Z i) (conj (Z i)) (k2 i : ℂ) (W i) (conj (W i))

/-- **The eliminated polynomial of a `K` component is not zero.** -/
theorem elimQK_ne_zero {k0 : ℝ} (hk0 : 0 < k0) (Z0 : ℂ) (b : ℕ → Bool) (k : ℕ → ℝ) (Z : ℕ → ℂ)
    (k2 : ℕ → ℝ) (W : ℕ → ℂ) (m : ℕ) (hadm : ∀ i < m, RespAdm (b i) (k i) (Z i) (k2 i) (W i)) :
    elimQK (k0 : ℂ) Z0 (kq b k Z k2 W) m ≠ 0 :=
  elimQK_ne_zero_of hk0 Z0 _ (fun _ => natDegree_qK_le _ _ _ _ _ _ _) m
    (fun i hi _ hε => qK_root_facts (hadm i hi) hε)

/-! ## A degree bound uniform in the data -/

/-- The universal data ring. -/
abbrev UnivRingK : Type := MvPolynomial (Fin 2 ⊕ ℕ × Fin 6) ℂ

/-- The universal response polynomials for port types `b`. -/
def univQ (b : ℕ → Bool) (i : ℕ) : UnivRingK[X][X] :=
  qK (b i) (MvPolynomial.X (Sum.inr (i, 0))) (MvPolynomial.X (Sum.inr (i, 1)))
    (MvPolynomial.X (Sum.inr (i, 2))) (MvPolynomial.X (Sum.inr (i, 3)))
    (MvPolynomial.X (Sum.inr (i, 4))) (MvPolynomial.X (Sum.inr (i, 5)))

/-- The eliminated polynomial for universal data. -/
def univElimQK (b : ℕ → Bool) (m : ℕ) : UnivRingK[X] :=
  elimQK (MvPolynomial.X (Sum.inl 0)) (MvPolynomial.X (Sum.inl 1)) (univQ b) m

/-- Port types on `Fin m`, extended by `false`. -/
def extB {m : ℕ} (b : Fin m → Bool) (i : ℕ) : Bool := if h : i < m then b ⟨i, h⟩ else false

/-- The uniform degree bound for `m` responses. -/
def capDegK (m : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin m → Bool)).sup (fun b => (univElimQK (extB b) m).natDegree)

lemma natDegree_elimQK_le (k0 Z0 : ℂ) (b : ℕ → Bool) (k Z Zc k2 W Wc : ℕ → ℂ) (m : ℕ) :
    (elimQK k0 Z0 (fun i => qK (b i) (k i) (Z i) (Zc i) (k2 i) (W i) (Wc i)) m).natDegree ≤
      capDegK m := by
  set b' : Fin m → Bool := fun i => b i
  have hb : ∀ i < m, b i = extB b' i := fun i hi => by simp [extB, hi, b']
  rw [elimQK_congr (q' := fun i => qK (extB b' i) (k i) (Z i) (Zc i) (k2 i) (W i) (Wc i))
    (fun i hi => by rw [hb i hi])]
  set φ : UnivRingK →+* ℂ := MvPolynomial.eval
    (Sum.elim ![k0, Z0] (fun p => ![k p.1, Z p.1, Zc p.1, k2 p.1, W p.1, Wc p.1] p.2))
  have h := elimQK_map φ (MvPolynomial.X (Sum.inl 0)) (MvPolynomial.X (Sum.inl 1))
    (univQ (extB b')) m
  have e : elimQK (φ (MvPolynomial.X (Sum.inl 0))) (φ (MvPolynomial.X (Sum.inl 1)))
      (fun i => (univQ (extB b') i).map (mapRingHom φ)) m =
      elimQK k0 Z0 (fun i => qK (extB b' i) (k i) (Z i) (Zc i) (k2 i) (W i) (Wc i)) m := by
    congr 1
    · simp [φ]
    · simp [φ]
    · funext i
      rw [univQ, qK_map]
      simp [φ]
  rw [← e, ← h]
  refine natDegree_map_le.trans ?_
  exact Finset.le_sup (f := fun b => (univElimQK (extB b) m).natDegree) (Finset.mem_univ b')

/-- The `J` response equation in polynomial form: if `|v| = 1`, `|p| = 1` and
`|p - (l ζ + Z + v)| = 1`, then `jQuad l Z ζ v p = 0`. -/
lemma jQuad_of_unit {l : ℝ} {ζ Z v p : ℂ} (hζ : ‖ζ‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (hpa : ‖p - ((l : ℂ) * ζ + (Z + v))‖ = 1) : jQuad l Z ζ v p = 0 := by
  have h := QuadraticResponse.two_circle_eq_poly l hζ hp hpa
  have hvv : conj v * v = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]; norm_num
  rw [jQuad, map_add] at *
  linear_combination v * h - ζ * (p ^ 2 - ((l : ℂ) * ζ + Z + v) * p) * hvv

/-- **Few exact solutions** for a `K` component (Verification Guide §13.4). -/
theorem capless_solutions_card_leK {k0 : ℝ} (hk0 : 0 < k0) (Z0 : ℂ) (b : ℕ → Bool) (k : ℕ → ℝ)
    (Z : ℕ → ℂ) (k2 : ℕ → ℝ) (W : ℕ → ℂ) (m : ℕ)
    (hadm : ∀ i < m, RespAdm (b i) (k i) (Z i) (k2 i) (W i)) :
    ∃ S : Finset ℂ, S.card ≤ capDegK m ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : ℕ → ℂ,
      (∀ i < m, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1 ∧
        (if b i then (k i : ℂ) * ζ + Z i - p i + v i + u i = 0 ∧
            (k2 i : ℂ) * ζ + W i - v i + w i = 0
          else (k i : ℂ) * ζ + Z i - p i + u i = 0)) →
      (k0 : ℂ) * ζ + Z0 + ∑ i ∈ Finset.range m, p i = 0 → ζ ∈ S := by
  set Q := elimQK (k0 : ℂ) Z0 (kq b k Z k2 W) m
  refine ⟨Q.roots.toFinset, (Multiset.toFinset_card_le _).trans
    ((card_roots' Q).trans (natDegree_elimQK_le _ _ b _ _ _ _ _ _ m)), fun ζ hζ p u v w hpu hsum => ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (elimQK_ne_zero hk0 Z0 b k Z k2 W m hadm)]
  show ((elimPK (kq b k Z k2 W) m).eval (respA (k0 : ℂ) Z0)).eval ζ = 0
  rw [eval_eval_eq_eval_map]
  refine elimPK_eval_eq_zero _ (fun _ => natDegree_qK_le _ _ _ _ _ _ _) ζ p m (fun i hi => ?_) _ ?_
  · obtain ⟨hp, hu, hv, hw, he⟩ := hpu i hi
    cases hb : b i
    · rw [hb] at he
      simp only [Bool.false_eq_true, if_false] at he
      simp only [qK, Bool.false_eq_true, if_false, Polynomial.map_pow, eval_pow]
      have hpa : ‖p i - ((k i : ℝ) * ζ + Z i)‖ = 1 := by
        rw [show p i - ((k i : ℝ) * ζ + Z i) = u i by linear_combination -he, hu]
      have := QuadraticResponse.two_circle_eq_poly (k i) hζ hp hpa
      rw [respQ_map_eval, pow_eq_zero_iff two_ne_zero]
      linear_combination this
    · rw [hb] at he
      simp only [if_true] at he
      simp only [qK, if_true]
      have hva : ‖v i - ((k2 i : ℝ) * ζ + W i)‖ = 1 := by
        rw [show v i - ((k2 i : ℝ) * ζ + W i) = w i by linear_combination -he.2, hw]
      have hH := QuadraticResponse.two_circle_eq_poly (k2 i) hζ hv hva
      have hpa : ‖p i - ((k i : ℝ) * ζ + (Z i + v i))‖ = 1 := by
        rw [show p i - ((k i : ℝ) * ζ + (Z i + v i)) = u i by linear_combination -he.1, hu]
      refine jQuartic_eval_eq_zero (v := v i) ?_ (jQuad_of_unit hζ hv hp hpa)
      rw [hQuad]
      linear_combination hH
  · simpa [respA] using hsum

end CaplessKElim

end Erdos99
end

end CaplessKPoly

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessKPinning`
-/

section CaplessKPinning

/-!
# Approximate `K`-component relations pin the direction (Verification Guide §12.4–§12.5)

* `CapDataK m`: the data `(k₀, Z₀, k, Z, k₂, W)` of the relations of a `K` component with `m`
  outgoing ports; port `i` ends at an `H` face (`b i = false`, data `k_i, Z_i`) or at a `J` face
  (`b i = true`, data `k_i, Z_i` of the `J` face and `k₂_i, W_i` of its chosen `H` neighbour);
* `capAdmK m R c b`: the compact set of admissible data (bounded, multiplicities in `{1, 2}`, and
  `‖Z_i‖ ≥ c`, `‖Z_i + W_i‖ ≥ c` at the `J` ports);
* `CapApproxK m r b d ζ`: `r`-approximate unit solutions of the relations
  `k₀ ζ + Z₀ + Σ p_i ≈ 0`, and `k_i ζ + Z_i - p_i + u_i ≈ 0` (`H` port) or
  `k_i ζ + Z_i - p_i + v_i + u_i ≈ 0`, `k₂_i ζ + W_i - v_i + w_i ≈ 0` (`J` port);
* `capless_pinningK`: a separated set of directions with approximate solutions for data close to
  one centre has at most `capDegK m` elements;
* `capless_directions_fewK`: the corresponding hull sides are at most `ε D`.
-/

open Filter Topology Metric ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace CaplessKElim

open CaplessElim

/-- The data of the relations of a `K` component with `m` outgoing ports. -/
abbrev CapDataK (m : ℕ) : Type :=
  ℝ × ℂ × (Fin m → ℝ) × (Fin m → ℂ) × (Fin m → ℝ) × (Fin m → ℂ)

/-- The bounded part of the admissible data. -/
def capBoxK (m : ℕ) (R : ℝ) : Set (CapDataK m) :=
  Set.Icc 1 R ×ˢ closedBall 0 R ×ˢ Set.univ.pi (fun _ => ({1, 2} : Set ℝ)) ×ˢ
    Set.univ.pi (fun _ => closedBall (0 : ℂ) R) ×ˢ Set.univ.pi (fun _ => ({1, 2} : Set ℝ)) ×ˢ
    Set.univ.pi (fun _ => closedBall (0 : ℂ) R)

/-- The three-port margins at the `J` ports. -/
def capMarginK (m : ℕ) (c : ℝ) (b : Fin m → Bool) : Set (CapDataK m) :=
  {d | ∀ i, b i = true → c ≤ ‖d.2.2.2.1 i‖ ∧ c ≤ ‖d.2.2.2.1 i + d.2.2.2.2.2 i‖}

/-- The admissible data. -/
def capAdmK (m : ℕ) (R c : ℝ) (b : Fin m → Bool) : Set (CapDataK m) :=
  capBoxK m R ∩ capMarginK m c b

lemma isCompact_capAdmK (m : ℕ) (R c : ℝ) (b : Fin m → Bool) : IsCompact (capAdmK m R c b) := by
  refine IsCompact.inter_right ?_ ?_
  · exact isCompact_Icc.prod ((isCompact_closedBall _ _).prod
      ((isCompact_univ_pi fun _ => (Set.toFinite _).isCompact).prod
        ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod
          ((isCompact_univ_pi fun _ => (Set.toFinite _).isCompact).prod
            (isCompact_univ_pi fun _ => isCompact_closedBall _ _)))))
  · have e : capMarginK m c b = ⋂ i, ⋂ (_ : b i = true),
        ({d : CapDataK m | c ≤ ‖d.2.2.2.1 i‖} ∩ {d | c ≤ ‖d.2.2.2.1 i + d.2.2.2.2.2 i‖}) := by
      ext d; simp [capMarginK]
    rw [e]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact (isClosed_le continuous_const
        (by fun_prop : Continuous fun d : CapDataK m => ‖d.2.2.2.1 i‖)).inter
      (isClosed_le continuous_const
        (by fun_prop : Continuous fun d : CapDataK m => ‖d.2.2.2.1 i + d.2.2.2.2.2 i‖))

/-- The residual of the component relation. -/
def capRes0K {m : ℕ} (d : CapDataK m) (ζ : ℂ) (p : Fin m → ℂ) : ℝ :=
  ‖(d.1 : ℂ) * ζ + d.2.1 + ∑ i, p i‖

/-- The residual of the relations at port `i`. -/
def capRes1K {m : ℕ} (b : Fin m → Bool) (d : CapDataK m) (ζ : ℂ) (p u v w : Fin m → ℂ)
    (i : Fin m) : ℝ :=
  if b i then ‖(d.2.2.1 i : ℂ) * ζ + d.2.2.2.1 i - p i + v i + u i‖ +
      ‖(d.2.2.2.2.1 i : ℂ) * ζ + d.2.2.2.2.2 i - v i + w i‖
  else ‖(d.2.2.1 i : ℂ) * ζ + d.2.2.2.1 i - p i + u i‖

/-- `r`-approximate unit solutions of the relations of a `K` component at the direction `ζ`. -/
def CapApproxK (m : ℕ) (r : ℝ) (b : Fin m → Bool) (d : CapDataK m) (ζ : ℂ) : Prop :=
  ∃ p u v w : Fin m → ℂ, (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1) ∧
    capRes0K d ζ p < r ∧ ∀ i, capRes1K b d ζ p u v w i < r

/-- Exact solutions for admissible data lie in a set of at most `capDegK m` directions. -/
lemma exact_solutions_card_leK (m : ℕ) (R : ℝ) {c : ℝ} (hc : 0 < c) (b : Fin m → Bool)
    {d : CapDataK m} (hd : d ∈ capAdmK m R c b) :
    ∃ S : Finset ℂ, S.card ≤ capDegK m ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : Fin m → ℂ,
      (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1) → capRes0K d ζ p = 0 →
      (∀ i, capRes1K b d ζ p u v w i = 0) → ζ ∈ S := by
  obtain ⟨⟨⟨hk1, -⟩, -, hk, -, hk2, -⟩, hmar⟩ := hd
  set ext : (Fin m → ℂ) → ℕ → ℂ := fun f i => if h : i < m then f ⟨i, h⟩ else 0 with hext
  set extR : (Fin m → ℝ) → ℕ → ℝ := fun f i => if h : i < m then f ⟨i, h⟩ else 1 with hextR
  have hadm : ∀ i < m, RespAdm (extB b i) (extR d.2.2.1 i) (ext d.2.2.2.1 i)
      (extR d.2.2.2.2.1 i) (ext d.2.2.2.2.2 i) := by
    intro i hi
    simp only [extB, extR, ext, dif_pos hi]
    refine ⟨hk ⟨i, hi⟩ (Set.mem_univ _), fun hb => ⟨hk2 ⟨i, hi⟩ (Set.mem_univ _), ?_, ?_⟩⟩
    · intro h0
      have := (hmar ⟨i, hi⟩ hb).1
      rw [h0, norm_zero] at this; linarith
    · intro h0
      have := (hmar ⟨i, hi⟩ hb).2
      rw [h0, norm_zero] at this; linarith
  obtain ⟨S, hS, hsol⟩ := capless_solutions_card_leK (by linarith : (0 : ℝ) < d.1) d.2.1 (extB b)
    (extR d.2.2.1) (ext d.2.2.2.1) (extR d.2.2.2.2.1) (ext d.2.2.2.2.2) m hadm
  refine ⟨S, hS, fun ζ hζ p u v w hpu h0 h1 => ?_⟩
  refine hsol ζ hζ (ext p) (ext u) (ext v) (ext w) (fun i hi => ?_) ?_
  · simp only [extB, extR, ext, dif_pos hi]
    obtain ⟨h1p, h1u, h1v, h1w⟩ := hpu ⟨i, hi⟩
    refine ⟨h1p, h1u, h1v, h1w, ?_⟩
    have h := h1 ⟨i, hi⟩
    unfold capRes1K at h
    split_ifs at h ⊢ with hb
    · have ha := norm_nonneg ((d.2.2.1 ⟨i, hi⟩ : ℂ) * ζ + d.2.2.2.1 ⟨i, hi⟩ - p ⟨i, hi⟩ +
        v ⟨i, hi⟩ + u ⟨i, hi⟩)
      have hb' := norm_nonneg ((d.2.2.2.2.1 ⟨i, hi⟩ : ℂ) * ζ + d.2.2.2.2.2 ⟨i, hi⟩ - v ⟨i, hi⟩ +
        w ⟨i, hi⟩)
      exact ⟨norm_eq_zero.1 (by linarith), norm_eq_zero.1 (by linarith)⟩
    · exact norm_eq_zero.1 h
  · have : ∑ i ∈ Finset.range m, ext p i = ∑ i, p i := by
      rw [Finset.sum_range (fun i => ext p i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ext, i.2]
    rw [this]
    exact norm_eq_zero.1 h0

/-- The state of one approximate solution. -/
abbrev CapStateK (m : ℕ) : Type :=
  CapDataK m × ℂ × (Fin m → ℂ) × (Fin m → ℂ) × (Fin m → ℂ) × (Fin m → ℂ)

/-- The compact set of admissible states. -/
def capStatesK (m : ℕ) (R c : ℝ) (b : Fin m → Bool) : Set (CapStateK m) :=
  capAdmK m R c b ×ˢ sphere 0 1 ×ˢ Set.univ.pi (fun _ => sphere (0 : ℂ) 1) ×ˢ
    Set.univ.pi (fun _ => sphere (0 : ℂ) 1) ×ˢ Set.univ.pi (fun _ => sphere (0 : ℂ) 1) ×ˢ
    Set.univ.pi (fun _ => sphere (0 : ℂ) 1)

lemma isCompact_capStatesK (m : ℕ) (R c : ℝ) (b : Fin m → Bool) :
    IsCompact (capStatesK m R c b) :=
  (isCompact_capAdmK m R c b).prod ((isCompact_sphere _ _).prod
    ((isCompact_univ_pi fun _ => isCompact_sphere _ _).prod
      ((isCompact_univ_pi fun _ => isCompact_sphere _ _).prod
        ((isCompact_univ_pi fun _ => isCompact_sphere _ _).prod
          (isCompact_univ_pi fun _ => isCompact_sphere _ _)))))

lemma continuous_capRes0K (m : ℕ) :
    Continuous (fun s : CapStateK m => capRes0K s.1 s.2.1 s.2.2.1) := by
  unfold capRes0K
  fun_prop

lemma continuous_capRes1K (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    Continuous (fun s : CapStateK m =>
      capRes1K b s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 i) := by
  unfold capRes1K
  cases b i
  · simp only [Bool.false_eq_true, if_false]; fun_prop
  · simp only [if_true]; fun_prop

set_option synthInstance.maxSize 512 in
/-- **Approximate `K`-component relations pin the direction** (compactness). -/
theorem capless_pinningK (m : ℕ) (R : ℝ) {c : ℝ} (hc : 0 < c) (b : Fin m → Bool) {w : ℝ}
    (hw : 0 < w) :
    ∃ r > 0, ∃ μ > 0, ∀ (c' : CapDataK m) (A : Finset ℂ),
      (∀ ζ ∈ A, ‖ζ‖ = 1 ∧ ∃ d ∈ capAdmK m R c b, ‖d - c'‖ < μ ∧ CapApproxK m r b d ζ) →
      (A : Set ℂ).Pairwise (fun a b => w ≤ ‖a - b‖) → A.card ≤ capDegK m := by
  set N := capDegK m
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ s : Fin (N + 1) → CapStateK m, (∀ j, s j ∈ capStatesK m R c b) ∧
      (∀ j j', ‖(s j).1 - (s j').1‖ < 2 / (n + 1)) ∧
      (∀ j j', j ≠ j' → w ≤ ‖(s j).2.1 - (s j').2.1‖) ∧
      (∀ j, capRes0K (s j).1 (s j).2.1 (s j).2.2.1 < 1 / (n + 1)) ∧
      (∀ j i, capRes1K b (s j).1 (s j).2.1 (s j).2.2.1 (s j).2.2.2.1 (s j).2.2.2.2.1
        (s j).2.2.2.2.2 i < 1 / (n + 1)) := by
    intro n
    obtain ⟨c', A, hA, hsep, hcard⟩ := hcon (1 / (n + 1)) (by positivity) (1 / (n + 1))
      (by positivity)
    obtain ⟨A', hA'A, hA'card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcard)
    set e := A'.equivFin
    have hmem : ∀ j : Fin (N + 1), ((e.symm (Fin.cast hA'card.symm j)) : ℂ) ∈ A :=
      fun j => hA'A (e.symm _).2
    choose hζ1 d hdK hdc p u v w' hpu h0 h1 using fun j => hA _ (hmem j)
    refine ⟨fun j => (d j, (e.symm (Fin.cast hA'card.symm j) : ℂ), p j, u j, v j, w' j),
      fun j => ?_, fun j j' => ?_, fun j j' hjj' => ?_, fun j => h0 j, fun j i => h1 j i⟩
    · refine ⟨hdK j, ?_, fun i _ => ?_, fun i _ => ?_, fun i _ => ?_, fun i _ => ?_⟩
      · simpa using hζ1 j
      · simpa using (hpu j i).1
      · simpa using (hpu j i).2.1
      · simpa using (hpu j i).2.2.1
      · simpa using (hpu j i).2.2.2
    · calc ‖d j - d j'‖ = ‖(d j - c') - (d j' - c')‖ := by congr 1; abel
        _ ≤ ‖d j - c'‖ + ‖d j' - c'‖ := norm_sub_le _ _
        _ < 1 / (n + 1) + 1 / (n + 1) := add_lt_add (hdc j) (hdc j')
        _ = 2 / (n + 1) := by ring
    · refine hsep (Finset.mem_coe.2 (hmem j)) (Finset.mem_coe.2 (hmem j')) ?_
      intro heq
      apply hjj'
      have := Subtype.ext heq
      have := e.symm.injective this
      exact Fin.cast_injective _ this
  choose s hsK hsd hsw hs0 hs1 using hseq
  have hK : IsCompact (Set.univ.pi fun _ : Fin (N + 1) => capStatesK m R c b) :=
    isCompact_univ_pi fun _ => isCompact_capStatesK m R c b
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
      simpa [mul_one_div] using hinv.const_mul 2
    exact sub_eq_zero.1 (tendsto_nhds_unique ht ht0)
  have hres0 : ∀ j, capRes0K (a j).1 (a j).2.1 (a j).2.2.1 = 0 := by
    intro j
    have ht := ((continuous_capRes0K m).tendsto _).comp (hlimj j)
    refine le_antisymm (le_of_tendsto_of_tendsto' ht hinv fun n => (hs0 (φ n) j).le) ?_
    exact norm_nonneg _
  have hres1 : ∀ j i, capRes1K b (a j).1 (a j).2.1 (a j).2.2.1 (a j).2.2.2.1 (a j).2.2.2.2.1
      (a j).2.2.2.2.2 i = 0 := by
    intro j i
    have ht := ((continuous_capRes1K m b i).tendsto _).comp (hlimj j)
    refine le_antisymm (le_of_tendsto_of_tendsto' ht hinv fun n => (hs1 (φ n) j i).le) ?_
    unfold capRes1K
    split_ifs <;> positivity
  have hsep : ∀ j j', j ≠ j' → w ≤ ‖(a j).2.1 - (a j').2.1‖ := by
    intro j j' hjj'
    have ht : Tendsto (fun n => ‖(s (φ n) j).2.1 - (s (φ n) j').2.1‖) atTop
        (𝓝 ‖(a j).2.1 - (a j').2.1‖) :=
      (((continuous_fst.comp continuous_snd).tendsto _).comp (hlimj j)).sub
        (((continuous_fst.comp continuous_snd).tendsto _).comp (hlimj j')) |>.norm
    exact ge_of_tendsto' ht fun n => hsw (φ n) j j' hjj'
  obtain ⟨S, hS, hsol⟩ := exact_solutions_card_leK m R hc b (ha 0 (Set.mem_univ _)).1
  have hmemS : ∀ j, (a j).2.1 ∈ S := by
    intro j
    have hj := ha j (Set.mem_univ _)
    obtain ⟨-, hζ, hp, hu, hv, hw'⟩ := hj
    refine hsol _ (by simpa using hζ) (a j).2.2.1 (a j).2.2.2.1 (a j).2.2.2.2.1 (a j).2.2.2.2.2
      (fun i => ⟨by simpa using hp i (Set.mem_univ _), by simpa using hu i (Set.mem_univ _),
        by simpa using hv i (Set.mem_univ _), by simpa using hw' i (Set.mem_univ _)⟩) ?_ ?_
    · rw [← hdata j]; exact hres0 j
    · intro i; rw [← hdata j]; exact hres1 j i
  have hinj : Function.Injective (fun j => (a j).2.1) := by
    intro j j' h
    by_contra hne
    have := hsep j j' hne
    simp only at h
    rw [h, sub_self, norm_zero] at this
    linarith
  have := Finset.card_le_card_of_injOn (s := Finset.univ) (fun j => (a j).2.1)
    (fun j _ => hmemS j) hinj.injOn
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **Hull directions pinned by `K`-component relations are few.** -/
theorem capless_directions_fewK (m : ℕ) (R : ℝ) {c : ℝ} (hc : 0 < c) (Nc : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ Cs : Finset (CapDataK m), Cs.card ≤ Nc →
      ∀ A ⊆ ccwHullSides X, (∀ p ∈ A, ∃ b : Fin m → Bool, ∃ d ∈ capAdmK m R c b,
        (∃ c' ∈ Cs, ‖d - c'‖ < μ) ∧ CapApproxK m r b d (toC (sideDir p))) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨C, hC, hcount⟩ := card_sides_near_finset
  set K : ℝ := 2 ^ m * Nc * capDegK m with hK
  have hK0 : 0 ≤ K := by positivity
  set w : ℝ := min 1 (ε / (2 * (C * K + 1))) with hw
  have hw0 : 0 < w := lt_min one_pos (by positivity)
  have hw1 : w ≤ 1 := min_le_left _ _
  choose rb hrb μb hμb hpin using fun b : Fin m → Bool => capless_pinningK m R hc b hw0
  have hI : (Finset.univ : Finset (Fin m → Bool)).Nonempty := Finset.univ_nonempty
  obtain ⟨r, hr, hrm⟩ : ∃ r > 0, ∀ b, r ≤ rb b :=
    ⟨_, (Finset.lt_inf'_iff hI).2 fun b _ => hrb b, fun b => Finset.inf'_le _ (Finset.mem_univ b)⟩
  obtain ⟨μ, hμ, hμm⟩ : ∃ μ > 0, ∀ b, μ ≤ μb b :=
    ⟨_, (Finset.lt_inf'_iff hI).2 fun b _ => hμb b, fun b => Finset.inf'_le _ (Finset.mem_univ b)⟩
  refine ⟨r, hr, μ, hμ, ?_⟩
  have hsmall : ∀ᶠ n in atTop, minDiam n ^ (-(1 / 9 : ℝ)) ≤ w :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp tendsto_minDiam).eventually
      (Iic_mem_nhds hw0)
  filter_upwards [hcount, hsmall] with n hn hsm X hX Cs hCs A hA hpA
  rw [← hX.diam_eq] at hsm
  set T : (Fin m → Bool) → CapDataK m → Finset ℂ := fun b c' =>
    (A.filter (fun p => ∃ d ∈ capAdmK m R c b, ‖d - c'‖ < μb b ∧
      CapApproxK m (rb b) b d (toC (sideDir p)))).image (fun p => toC (sideDir p))
  have hunit : ∀ p ∈ A, ‖toC (sideDir p)‖ = 1 := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 (hA hp)).2.2.2.1
    rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
  choose! Sc hScT hScsep hScdense using fun b c' => CaplessElim.exists_maximal_separated (T b c') hw0
  have hSccard : ∀ b c', (Sc b c').card ≤ capDegK m := by
    intro b c'
    refine hpin b c' (Sc b c') (fun ζ hζ => ?_) (hScsep b c')
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (hScT b c' hζ)
    obtain ⟨hpA', d, hd, hdc, hap⟩ := Finset.mem_filter.1 hp
    exact ⟨hunit p hpA', d, hd, hdc, hap⟩
  set S : Finset ℂ := (Finset.univ : Finset (Fin m → Bool)).biUnion
    (fun b => Cs.biUnion (Sc b)) with hS
  have hScard : (S.card : ℝ) ≤ K := by
    have h1 : S.card ≤ 2 ^ m * (Nc * capDegK m) := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ b : Fin m → Bool, (Cs.biUnion (Sc b)).card ≤ ∑ _b : Fin m → Bool, Nc * capDegK m := by
            refine Finset.sum_le_sum fun b _ => Finset.card_biUnion_le.trans ?_
            calc ∑ c' ∈ Cs, (Sc b c').card ≤ ∑ _c' ∈ Cs, capDegK m :=
                  Finset.sum_le_sum fun c' _ => hSccard b c'
              _ = Cs.card * capDegK m := by simp
              _ ≤ Nc * capDegK m := Nat.mul_le_mul_right _ hCs
        _ = 2 ^ m * (Nc * capDegK m) := by simp
    rw [hK]
    have : ((2 ^ m * (Nc * capDegK m) : ℕ) : ℝ) = 2 ^ m * Nc * capDegK m := by push_cast; ring
    rw [← this]; exact_mod_cast h1
  have hsub : A ⊆ (ccwHullSides X).filter (fun p => ∃ s ∈ S, ‖toC (sideDir p) - s‖ ≤ w) := by
    intro p hp
    refine Finset.mem_filter.2 ⟨hA hp, ?_⟩
    obtain ⟨b, d, hd, ⟨c', hc', hdc⟩, hap⟩ := hpA p hp
    have hap' : CapApproxK m (rb b) b d (toC (sideDir p)) := by
      obtain ⟨pp, uu, vv, ww, h1, h2, h3⟩ := hap
      exact ⟨pp, uu, vv, ww, h1, h2.trans_le (hrm b), fun i => (h3 i).trans_le (hrm b)⟩
    have hT : toC (sideDir p) ∈ T b c' :=
      Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp, d, hd, hdc.trans_le (hμm b), hap'⟩, rfl⟩
    obtain ⟨s, hs, hps⟩ := hScdense b c' _ hT
    exact ⟨s, Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c', hc', hs⟩⟩,
      hps.le⟩
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

end CaplessKElim

end Erdos99
end

end CaplessKPinning

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessKPorts`
-/

section CaplessKPorts

/-!
# Capless components of `K`: the relations at one outgoing port (Verification Guide §13.4)

* `jSel F`: a chosen matched port of a `J` face `F` whose mate is a degree-two face;
* `portB q`: whether the outgoing port `q` ends at a `J` face;
* `hFace q`: the degree-two face reached from the `J` face at the end of `q` through `jSel`;
* `port_relation_K`: the relations at an outgoing port, with an `H` or a `J` receiver;
* `port_margin_K`: the three-port margin of the data at a `J` receiver.
-/

open scoped BigOperators Real
open Filter ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim CaplessKElim

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

/-- A chosen matched port of the face `F` whose mate is a degree-two face (if there is one). -/
def jSel (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (F : Set ℂ) : Set ℂ × Sym2 Plane :=
  if h : ∃ q' ∈ unmarkedPorts X L G mk, q'.1 = F ∧ TrackMated X L G mk q' ∧
      (trackMate X q').1 ∈ (trackGraph X L G mk).Hs G.good then h.choose else (∅, s(0, 0))

lemma jSel_spec (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {F : Set ℂ}
    (hF : F ∈ (trackGraph X L G mk).Js G.good) :
    jSel X L G mk F ∈ unmarkedPorts X L G mk ∧ (jSel X L G mk F).1 = F ∧
      TrackMated X L G mk (jSel X L G mk F) ∧
      (trackMate X (jSel X L G mk F)).1 ∈ (trackGraph X L G mk).Hs G.good := by
  have h := exists_H_incidence hends hF
  rw [jSel, dif_pos h]
  exact h.choose_spec

/-- Whether the outgoing port `q` ends at a `J` face. -/
def portB (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (q : Set ℂ × Sym2 Plane) : Bool :=
  decide ((trackMate X q).1 ∈ (trackGraph X L G mk).Js G.good)

/-- The degree-two face reached from the `J` face at the end of `q`. -/
def hFace (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (q : Set ℂ × Sym2 Plane) : Set ℂ :=
  (trackMate X (jSel X L G mk (trackMate X q).1)).1

lemma Hs_Js_disjoint {F : Set ℂ} (hH : F ∈ (trackGraph X L G mk).Hs G.good)
    (hJ : F ∈ (trackGraph X L G mk).Js G.good) : False := by
  have h1 := (Finset.mem_filter.1 hH).2
  have h2 := (Finset.mem_filter.1 hJ).2.1
  omega

/-- **The relations at one outgoing port.** -/
theorem port_relation_K :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol ρ : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane) (ζ : ℂ), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        q.1 ∉ (trackGraph X L G mk).Hs G.good →
        ((trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good ∨
          (trackMate X q).1 ∈ (trackGraph X L G mk).Js G.good) →
        ‖labDir lab (trackMate X q).1 - ζ‖ ≤ ρ →
        (portB X L G mk q = true → ‖labDir lab (hFace X L G mk q) - ζ‖ ≤ ρ) →
        ∃ u v w : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
          (if portB X L G mk q = true then
            ‖(G.kMult (trackMate X q).1 : ℂ) * ζ + longSum X L (trackMate X q).1 - portVec X q +
                v + u‖ +
              ‖(G.kMult (hFace X L G mk q) : ℂ) * ζ + longSum X L (hFace X L G mk q) - v + w‖
          else ‖(G.kMult (trackMate X q).1 : ℂ) * ζ + longSum X L (trackMate X q).1 -
                portVec X q + u‖) ≤ 2 * tol + 4 * ρ := by
  filter_upwards [ext_H_equation, ext_J_equation, card_trackEnds, exists_side_of_port,
    face_side_facts] with n hextH hextJ hends hside hfacts hfm X hX htri L tol ρ G mk lab ζ hmk
    hlab q hq hm hqH hcase hloc hloc'
  have hk2 : ∀ F, ‖(G.kMult F : ℂ)‖ ≤ 2 := fun F => by
    rcases G.kMult_cases F with h | h <;> rw [h] <;> norm_num
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hloc
  have htol0 : 0 ≤ tol := le_trans (norm_nonneg _) (hlab.2 q.1 (mem_unmarkedPorts.1 hq).1).2.1
  -- replacing a label direction by `ζ`
  have hrepl : ∀ (F : Set ℂ) (x : ℂ), ‖labDir lab F - ζ‖ ≤ ρ →
      ‖(G.kMult F : ℂ) * ζ + x‖ ≤ ‖(G.kMult F : ℂ) * labDir lab F + x‖ + 2 * ρ := by
    intro F x h
    have e : (G.kMult F : ℂ) * ζ + x = ((G.kMult F : ℂ) * labDir lab F + x) +
        (G.kMult F : ℂ) * (ζ - labDir lab F) := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_mul, norm_sub_rev]
    exact mul_le_mul (hk2 F) h (norm_nonneg _) (by norm_num)
  by_cases hb : portB X L G mk q = true
  · have hJ : (trackMate X q).1 ∈ (trackGraph X L G mk).Js G.good := by
      simpa [portB] using hb
    obtain ⟨hsP, hs1, hsm, hsH⟩ := jSel_spec (hends hfm X hX htri) hJ
    have hdeg : (trackGraph X L G mk).deg (trackMate X q).1 = 3 := (Finset.mem_filter.1 hJ).2.1
    have hne : jSel X L G mk (trackMate X q).1 ≠ trackMate X q := by
      intro h
      have hM := trackMate_isMatching (hends hfm X hX htri) L G mk
      have hinv := (hM q hq hm).2.2.1
      rw [h, hinv] at hsH
      exact hqH hsH
    obtain ⟨u, hu, hJeq⟩ := hextJ hfm X hX htri L tol G mk lab hmk hlab q hq hm hdeg _ hsP hs1 hne
    obtain ⟨w, hw, hHeq⟩ := hextH hfm X hX htri L tol G mk lab hmk hlab _ hsP hsm hsH
    -- the port vector of the selected port is a unit vector
    have hv : ‖portVec X (jSel X L G mk (trackMate X q).1)‖ = 1 := by
      obtain ⟨hFg, hsp, -⟩ := mem_unmarkedPorts.1 hsP
      obtain ⟨-, hpF, -⟩ := Finset.mem_filter.1 hsp
      obtain ⟨ab, hab, habe⟩ := hside hfm X hX _ _ hpF
      rw [portVec_eq (nonempty_of_mem_exceptionalFaces hpF.1) hab habe]
      exact (hfacts hfm X hX G _ hFg).2 ab hab
    refine ⟨u, portVec X (jSel X L G mk (trackMate X q).1), w, hu, hv, hw, ?_⟩
    rw [if_pos hb]
    have h1 := hrepl (trackMate X q).1 (longSum X L (trackMate X q).1 - portVec X q +
      portVec X (jSel X L G mk (trackMate X q).1) + u) hloc
    have h2 := hrepl (hFace X L G mk q) (longSum X L (hFace X L G mk q) -
      portVec X (jSel X L G mk (trackMate X q).1) + w) (hloc' hb)
    have e1 : (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 +
        (longSum X L (trackMate X q).1 - portVec X q +
          portVec X (jSel X L G mk (trackMate X q).1) + u) =
        (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 - portVec X q +
          portVec X (jSel X L G mk (trackMate X q).1) + u + longSum X L (trackMate X q).1 := by
      ring
    have e2 : (G.kMult (hFace X L G mk q) : ℂ) * labDir lab (hFace X L G mk q) +
        (longSum X L (hFace X L G mk q) - portVec X (jSel X L G mk (trackMate X q).1) + w) =
        (G.kMult (trackMate X (jSel X L G mk (trackMate X q).1)).1 : ℂ) *
          labDir lab (trackMate X (jSel X L G mk (trackMate X q).1)).1 -
          portVec X (jSel X L G mk (trackMate X q).1) + w +
          longSum X L (trackMate X (jSel X L G mk (trackMate X q).1)).1 := by
      rw [hFace]; ring
    rw [e1] at h1
    rw [e2] at h2
    have e3 : (G.kMult (trackMate X q).1 : ℂ) * ζ + longSum X L (trackMate X q).1 - portVec X q +
        portVec X (jSel X L G mk (trackMate X q).1) + u =
        (G.kMult (trackMate X q).1 : ℂ) * ζ + (longSum X L (trackMate X q).1 - portVec X q +
          portVec X (jSel X L G mk (trackMate X q).1) + u) := by ring
    have e4 : (G.kMult (hFace X L G mk q) : ℂ) * ζ + longSum X L (hFace X L G mk q) -
        portVec X (jSel X L G mk (trackMate X q).1) + w =
        (G.kMult (hFace X L G mk q) : ℂ) * ζ + (longSum X L (hFace X L G mk q) -
          portVec X (jSel X L G mk (trackMate X q).1) + w) := by ring
    rw [e3, e4]
    linarith
  · have hH : (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good := by
      rcases hcase with h | h
      · exact h
      · exact absurd (by simpa [portB] using h) hb
    obtain ⟨u, hu, hHeq⟩ := hextH hfm X hX htri L tol G mk lab hmk hlab q hq hm hH
    refine ⟨u, 1, 1, hu, norm_one, norm_one, ?_⟩
    rw [if_neg hb]
    have h1 := hrepl (trackMate X q).1 (longSum X L (trackMate X q).1 - portVec X q + u) hloc
    have e1 : (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 +
        (longSum X L (trackMate X q).1 - portVec X q + u) =
        (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 - portVec X q + u +
          longSum X L (trackMate X q).1 := by ring
    rw [e1] at h1
    have e3 : (G.kMult (trackMate X q).1 : ℂ) * ζ + longSum X L (trackMate X q).1 - portVec X q +
        u = (G.kMult (trackMate X q).1 : ℂ) * ζ +
          (longSum X L (trackMate X q).1 - portVec X q + u) := by ring
    rw [e3]
    linarith

/-- **The three-port margin at a `J` receiver.** -/
theorem port_margin_K :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L ρ κ : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane) (ζ : ℂ), IsMarking X L G mk → 0 < κ → ‖ζ‖ = 1 → ρ ≤ κ →
      (∀ F ∈ G.good, ∀ ab ∈ longSides X L F,
        ((ab.2 - ab.1) * conj (labDir lab F)).re ≤ 1 / 2 - 2 * κ) →
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q → portB X L G mk q = true →
        ‖labDir lab (trackMate X q).1 - ζ‖ ≤ ρ → ‖labDir lab (hFace X L G mk q) - ζ‖ ≤ ρ →
        min 1 κ ≤ ‖longSum X L (trackMate X q).1‖ ∧
          min 1 κ ≤ ‖longSum X L (trackMate X q).1 + longSum X L (hFace X L G mk q)‖ := by
  filter_upwards [card_longSides_J, card_longSides_H, card_trackEnds, face_side_facts] with n hJc
    hHc hends hfacts hfm X hX htri L ρ κ G mk lab ζ hmk hκ hζ hρκ hmar q hq hm hb hloc hloc'
  have hJ : (trackMate X q).1 ∈ (trackGraph X L G mk).Js G.good := by simpa [portB] using hb
  obtain ⟨hsP, hs1, hsm, hsH⟩ := jSel_spec (hends hfm X hX htri) hJ
  have hFg : (trackMate X q).1 ∈ G.good := (Finset.mem_filter.1 hJ).1
  have hHg : hFace X L G mk q ∈ G.good := (Finset.mem_filter.1 hsH).1
  have hA := hJc hfm X hX htri L G mk hmk _ hFg (Finset.mem_filter.1 hJ).2.1
  have hB := hHc hfm X hX htri L G mk hmk _ hHg (Finset.mem_filter.1 hsH).2
  -- the margin relative to `ζ`
  have hshift : ∀ F ∈ G.good, ‖labDir lab F - ζ‖ ≤ ρ → ∀ ab ∈ longSides X L F,
      ((ab.2 - ab.1) * conj ζ).re ≤ 1 / 2 - κ := by
    intro F hF hFζ ab hab
    have hu : ‖ab.2 - ab.1‖ = 1 := (hfacts hfm X hX G F hF).2 ab (Finset.mem_filter.1 hab).1
    have e : (ab.2 - ab.1) * conj ζ = (ab.2 - ab.1) * conj (labDir lab F) +
        (ab.2 - ab.1) * conj (ζ - labDir lab F) := by rw [map_sub]; ring
    rw [e, Complex.add_re]
    have h1 := hmar F hF ab hab
    have h2 : ((ab.2 - ab.1) * conj (ζ - labDir lab F)).re ≤ ρ := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj, hu, one_mul, norm_sub_rev]; exact hFζ
    linarith
  have hunit : ∀ ab ∈ longSides X L (trackMate X q).1 ∪ longSides X L (hFace X L G mk q),
      ‖ab.2 - ab.1‖ = 1 := by
    intro ab hab
    rcases Finset.mem_union.1 hab with h | h
    · exact (hfacts hfm X hX G _ hFg).2 ab (Finset.mem_filter.1 h).1
    · exact (hfacts hfm X hX G _ hHg).2 ab (Finset.mem_filter.1 h).1
  have hm' : ∀ ab ∈ longSides X L (trackMate X q).1 ∪ longSides X L (hFace X L G mk q),
      ((ab.2 - ab.1) * conj ζ).re ≤ 1 / 2 - κ := by
    intro ab hab
    rcases Finset.mem_union.1 hab with h | h
    · exact hshift _ hFg hloc ab h
    · exact hshift _ hHg hloc' ab h
  exact JH_margin hκ hζ hA hB hunit hm'

end Erdos99
end

end CaplessKPorts

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessKMain`
-/

section CaplessKMain

/-!
# Capless components of `K`: the witness of a component (Verification Guide §13.4)

* `compDataK`: the data of the relations of a set of faces with enumerated outgoing ports;
* `capCentresK`: the centres of these data, built from the cluster centres of the long sides;
* `component_witnessK`: a capless set of faces of `K`, away from the exceptional faces of the
  clustering, produces admissible data close to a centre with an approximate solution at the label
  direction of any of its faces.
-/

open scoped BigOperators Real
open Filter ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim CaplessKElim

/-- The data of the relations of a set of faces `Cf` with outgoing ports enumerated by `e`. -/
def compDataK {X : Finset Plane} (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (Cf : Finset (Set ℂ)) {Ext : Finset (Set ℂ × Sym2 Plane)} {m : ℕ} (e : Ext ≃ Fin m) :
    CapDataK m :=
  (∑ F ∈ Cf, G.kMult F, ∑ F ∈ Cf, longSum X L F,
    fun i => G.kMult (trackMate X (e.symm i)).1, fun i => longSum X L (trackMate X (e.symm i)).1,
    fun i => if portB X L G mk (e.symm i) = true then G.kMult (hFace X L G mk (e.symm i)) else 1,
    fun i => if portB X L G mk (e.symm i) = true then longSum X L (hFace X L G mk (e.symm i))
      else 0)

/-- The centres of the data with `m` outgoing ports. -/
def capCentresK (U : Finset ℂ) (M m : ℕ) : Finset (CapDataK m) :=
  ((Finset.range (2 * M + 1)).image (fun j : ℕ => (j : ℝ))) ×ˢ sumCentresK U (6 * M) ×ˢ
    Fintype.piFinset (fun _ : Fin m => ({1, 2} : Finset ℝ)) ×ˢ
    Fintype.piFinset (fun _ : Fin m => sumCentresK U 6) ×ˢ
    Fintype.piFinset (fun _ : Fin m => ({1, 2} : Finset ℝ)) ×ˢ
    Fintype.piFinset (fun _ : Fin m => sumCentresK U 6)

/-- The bound on the number of centres. -/
def capNcentK (Nc M m : ℕ) : ℕ :=
  (2 * M + 1) * ((6 * M + 1) ^ Nc * (2 ^ m * ((7 ^ Nc) ^ m * (2 ^ m * (7 ^ Nc) ^ m))))

lemma card_capCentresK_le {U : Finset ℂ} {Nc : ℕ} (hU : U.card ≤ Nc) (M m : ℕ) :
    (capCentresK U M m).card ≤ capNcentK Nc M m := by
  unfold capCentresK capNcentK
  simp only [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have h1 : ((Finset.range (2 * M + 1)).image (fun j : ℕ => (j : ℝ))).card ≤ 2 * M + 1 :=
    Finset.card_image_le.trans (by simp)
  have h2 : (sumCentresK U (6 * M)).card ≤ (6 * M + 1) ^ Nc :=
    (card_sumCentresK_le U _).trans (Nat.pow_le_pow_right (by omega) hU)
  have h3 : (({1, 2} : Finset ℝ)).card ≤ 2 := Finset.card_le_two
  have h4 : (sumCentresK U 6).card ≤ 7 ^ Nc :=
    (card_sumCentresK_le U _).trans (Nat.pow_le_pow_right (by omega) hU)
  gcongr

lemma zero_mem_sumCentresK (U : Finset ℂ) (K : ℕ) : (0 : ℂ) ∈ sumCentresK U K :=
  Finset.mem_image.2 ⟨fun _ => 0, Finset.mem_univ _, by simp⟩

lemma capDataK_norm_lt {m : ℕ} {d c : CapDataK m} {μ : ℝ} (hμ : 0 < μ) (h1 : d.1 = c.1)
    (h2 : ‖d.2.1 - c.2.1‖ < μ) (h3 : d.2.2.1 = c.2.2.1) (h4 : ∀ i, ‖d.2.2.2.1 i - c.2.2.2.1 i‖ < μ)
    (h5 : d.2.2.2.2.1 = c.2.2.2.2.1) (h6 : ∀ i, ‖d.2.2.2.2.2 i - c.2.2.2.2.2 i‖ < μ) :
    ‖d - c‖ < μ := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := d
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := c
  simp only at h1 h2 h3 h4 h5 h6
  subst h1 h3 h5
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
  refine max_lt hμ (max_lt h2 (max_lt hμ (max_lt ((pi_norm_lt_iff hμ).2 fun i => ?_)
    (max_lt hμ ((pi_norm_lt_iff hμ).2 fun i => ?_)))))
  · simpa using h4 i
  · simpa using h6 i

/-- **A capless set of faces of `K` gives a pinned direction.** -/
theorem component_witnessK :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L Λ tol ρ cρ εc μ0 r0 κ : ℝ) (M : ℕ) (G : GoodFaces X)
        (mk : Set ℂ → Finset (Sym2 Plane)) (lab : Set ℂ → Plane × Plane) (Ucl : Finset ℂ)
        (Bad : Finset (Set ℂ)),
      IsMarking X L G mk → NoIntermediatePorts X L Λ G → LabelledBy X tol G mk lab →
      (∀ F ∈ exceptionalFaces X, F ∉ Bad → ∀ ab ∈ orientedSides X F,
        (∃ e ∈ unitEdges X, Sym2.map toC e = s(ab.1, ab.2) ∧ Λ ≤ trackLength X (allTrackOf X e)) →
        ∃ u ∈ Ucl, ‖(ab.2 - ab.1) - u‖ ≤ εc) →
      (∀ p ∈ ccwHullSides X, ∀ q ∈ ccwHullSides X, dist p.1 q.1 ≤ cρ * diam X →
        ‖toC (sideDir p) - toC (sideDir q)‖ ≤ ρ) →
      (∀ F ∈ G.good, ∀ ab ∈ longSides X L F,
        ((ab.2 - ab.1) * conj (labDir lab F)).re ≤ 1 / 2 - 2 * κ) →
      0 < κ → ρ ≤ κ →
      (M + 2) * (2 * tol * diam X + 1 + L) ≤ cρ * diam X →
      M * tol + 2 * M * ρ < r0 → 2 * tol + 4 * ρ < r0 → 6 * M * εc < μ0 → 0 < μ0 → 0 ≤ εc →
      0 ≤ tol → 0 ≤ L →
      ∀ (Cf : Finset (Set ℂ)) (F0 : Set ℂ), F0 ∈ Cf → Cf ⊆ G.good → Cf.card ≤ M →
      (∀ F ∈ Cf, F ∉ (trackGraph X L G mk).Hs G.good) →
      (∀ F ∈ Cf, F ∉ Bad) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Bad) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → portB X L G mk q = true →
        hFace X L G mk q ∉ Bad) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → TrackMated X L G mk q) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Cf →
        (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good ∨
          (trackMate X q).1 ∈ (trackGraph X L G mk).Js G.good) →
      (∀ F ∈ Cf, dist (lab F0).1 (lab F).1 ≤ M * (2 * tol * diam X + 1 + L)) →
      ∃ b : Fin (extPorts X L G mk Cf).card → Bool,
        ∃ d ∈ capAdmK (extPorts X L G mk Cf).card (6 * M + 6) (min 1 κ) b,
        (∃ c ∈ capCentresK Ucl M (extPorts X L G mk Cf).card, ‖d - c‖ < μ0) ∧
        CapApproxK (extPorts X L G mk Cf).card r0 b d (labDir lab F0) := by
  filter_upwards [set_closure, port_relation_K, port_margin_K, face_side_facts, mated_label_dist,
    card_trackEnds, exists_side_of_port] with n hclo hrel hmarg hfacts hmld hends hside hfm X hX
    htri L Λ tol ρ cρ εc μ0 r0 κ M G mk lab Ucl Bad hmk hnoint hlab hcl hclose hmar hκ hρκ hpar
    hr1 hr2 hμ1 hμ0 hεc htol hL Cf F0 hF0 hCf hCM hCfH hnB hnB' hnB'' hmat hext hdist
  set D := diam X with hDdef
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  set δ0 := 2 * tol * D + 1 + L with hδ0
  have hδ0nn : 0 ≤ δ0 := by positivity
  have hccw : ∀ F ∈ G.good, lab F ∈ ccwHullSides X := fun F hF =>
    (Finset.mem_filter.1 (hlab.2 F hF).1).1
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hloc : ∀ F ∈ Cf, ‖labDir lab F - labDir lab F0‖ ≤ ρ := by
    intro F hF
    refine hclose _ (hccw F (hCf hF)) _ (hccw F0 (hCf hF0)) ?_
    rw [dist_comm]
    have := hdist F hF
    nlinarith
  have hρ0 : 0 ≤ ρ := by have := hloc F0 hF0; rw [sub_self, norm_zero] at this; exact this
  have hζ : ‖labDir lab F0‖ = 1 := by
    have hne : (lab F0).1 ≠ (lab F0).2 := (Finset.mem_filter.1 (hccw F0 (hCf hF0))).2.2.2.1
    rw [labDir, LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
  -- the receivers and their labels
  have hloc' : ∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf →
      ‖labDir lab (trackMate X q).1 - labDir lab F0‖ ≤ ρ ∧
      (portB X L G mk q = true → ‖labDir lab (hFace X L G mk q) - labDir lab F0‖ ≤ ρ) := by
    intro q hq hqC
    have hm := hmat q hq hqC
    obtain ⟨hg', -, -⟩ := mem_unmarkedPorts.1 hm.2
    have h1 := hmld hfm X hX htri L tol G mk lab hlab q hq hm
    have h2 := hdist q.1 hqC
    have hd1 : dist (lab (trackMate X q).1).1 (lab F0).1 ≤ δ0 + M * δ0 := by
      calc dist (lab (trackMate X q).1).1 (lab F0).1 ≤
          dist (lab (trackMate X q).1).1 (lab q.1).1 + dist (lab q.1).1 (lab F0).1 :=
            dist_triangle _ _ _
        _ ≤ δ0 + M * δ0 := by
          rw [← hDdef, ← hδ0, dist_comm] at h1; rw [dist_comm] at h2; linarith
    refine ⟨hclose _ (hccw _ hg') _ (hccw F0 (hCf hF0)) (by nlinarith), fun hb => ?_⟩
    have hJ : (trackMate X q).1 ∈ (trackGraph X L G mk).Js G.good := by simpa [portB] using hb
    obtain ⟨hsP, hs1, hsm, hsH⟩ := jSel_spec (hends hfm X hX htri) hJ
    have hHg : hFace X L G mk q ∈ G.good := (Finset.mem_filter.1 hsH).1
    have h3 := hmld hfm X hX htri L tol G mk lab hlab _ hsP hsm
    rw [hs1] at h3
    refine hclose _ (hccw _ hHg) _ (hccw F0 (hCf hF0)) ?_
    calc dist (lab (hFace X L G mk q)).1 (lab F0).1 ≤
        dist (lab (hFace X L G mk q)).1 (lab (trackMate X q).1).1 +
          dist (lab (trackMate X q).1).1 (lab F0).1 := dist_triangle _ _ _
      _ ≤ δ0 + (δ0 + M * δ0) := by
        rw [← hDdef, ← hδ0, dist_comm] at h3
        exact add_le_add h3 hd1
      _ ≤ cρ * D := by nlinarith
  set e := (extPorts X L G mk Cf).equivFin
  set m := (extPorts X L G mk Cf).card
  have hExtP : ∀ i : Fin m, (e.symm i : Set ℂ × Sym2 Plane) ∈ unmarkedPorts X L G mk ∧
      (e.symm i : Set ℂ × Sym2 Plane).1 ∈ Cf ∧
      (trackMate X (e.symm i : Set ℂ × Sym2 Plane)).1 ∉ Cf := fun i => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (e.symm i).2; exact ⟨h1, h2⟩
  set b : Fin m → Bool := fun i => portB X L G mk (e.symm i)
  -- the relations at the ports
  have hport : ∀ i : Fin m, ∃ u v w : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      (if portB X L G mk (e.symm i) = true then
        ‖(G.kMult (trackMate X (e.symm i)).1 : ℂ) * labDir lab F0 +
            longSum X L (trackMate X (e.symm i)).1 - portVec X (e.symm i) + v + u‖ +
          ‖(G.kMult (hFace X L G mk (e.symm i)) : ℂ) * labDir lab F0 +
            longSum X L (hFace X L G mk (e.symm i)) - v + w‖
      else ‖(G.kMult (trackMate X (e.symm i)).1 : ℂ) * labDir lab F0 +
          longSum X L (trackMate X (e.symm i)).1 - portVec X (e.symm i) + u‖) ≤
        2 * tol + 4 * ρ := by
    intro i
    obtain ⟨hq, hq1, hq2⟩ := hExtP i
    exact hrel hfm X hX htri L tol ρ G mk lab (labDir lab F0) hmk hlab _ hq (hmat _ hq hq1)
      (hCfH _ hq1) (hext _ hq hq1 hq2) (hloc' _ hq hq1).1 (hloc' _ hq hq1).2
  choose u v w hu hv hw hres using hport
  -- basic bounds
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
  have hkc : ∀ F, G.kMult F ∈ ({1, 2} : Set ℝ) := fun F => by
    rcases G.kMult_cases F with h | h <;> simp [h]
  have hkc' : ∀ F, G.kMult F ∈ ({1, 2} : Finset ℝ) := fun F => by
    rcases G.kMult_cases F with h | h <;> simp [h]
  have hrecv : ∀ i : Fin m, (trackMate X (e.symm i)).1 ∈ G.good ∧
      (trackMate X (e.symm i)).1 ∉ Bad := by
    intro i
    obtain ⟨hq, hq1, -⟩ := hExtP i
    exact ⟨(mem_unmarkedPorts.1 (hmat _ hq hq1).2).1, hnB' _ hq hq1⟩
  have hrecvH : ∀ i : Fin m, b i = true → hFace X L G mk (e.symm i) ∈ G.good ∧
      hFace X L G mk (e.symm i) ∉ Bad := by
    intro i hb
    obtain ⟨hq, hq1, -⟩ := hExtP i
    have hJ : (trackMate X (e.symm i)).1 ∈ (trackGraph X L G mk).Js G.good := by
      simpa [portB, b] using hb
    obtain ⟨-, -, -, hsH⟩ := jSel_spec (hends hfm X hX htri) hJ
    exact ⟨(Finset.mem_filter.1 hsH).1, hnB'' _ hq hq1 hb⟩
  -- the centres
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
  have hcen : ∀ F ∈ G.good, F ∉ Bad → ∃ z ∈ sumCentresK Ucl 6, ‖longSum X L F - z‖ ≤ 6 * εc := by
    intro F hF hFB
    have := sum_near_sumCentresK (longSides X L F) (fun ab => ab.2 - ab.1) Ucl (K := 6) hεc
      (hcard6 F hF) (hlongcl F hF hFB)
    simpa [longSum] using this
  have hzi : ∀ i : Fin m, ∃ z ∈ sumCentresK Ucl 6,
      ‖longSum X L (trackMate X (e.symm i)).1 - z‖ ≤ 6 * εc :=
    fun i => hcen _ (hrecv i).1 (hrecv i).2
  choose z hz hzd using hzi
  have hwi : ∀ i : Fin m, ∃ z ∈ sumCentresK Ucl 6,
      ‖(if b i = true then longSum X L (hFace X L G mk (e.symm i)) else 0) - z‖ ≤ 6 * εc := by
    intro i
    by_cases hb : b i = true
    · rw [if_pos hb]; exact hcen _ (hrecvH i hb).1 (hrecvH i hb).2
    · rw [if_neg hb]; exact ⟨0, zero_mem_sumCentresK _ _, by simp; positivity⟩
  choose wz hwz hwzd using hwi
  set j : ℕ := ∑ F ∈ Cf, (if F ∈ G.hex then 2 else 1 : ℕ) with hj
  have hjk : (j : ℝ) = ∑ F ∈ Cf, G.kMult F := by
    rw [hj, Nat.cast_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    unfold GoodFaces.kMult; split_ifs <;> simp
  have hjM : j ≤ 2 * M := by
    have : j ≤ ∑ _F ∈ Cf, 2 := Finset.sum_le_sum fun F _ => by split_ifs <;> omega
    rw [Finset.sum_const, smul_eq_mul] at this
    omega
  have hμ6 : 6 * εc < μ0 := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans (Finset.card_pos.2 ⟨F0, hF0⟩) hCM
    nlinarith
  refine ⟨b, compDataK L G mk Cf e, ⟨⟨⟨?_, ?_⟩, ?_, fun i _ => hkc _, fun i _ => ?_,
    fun i _ => ?_, fun i _ => ?_⟩, fun i hb => ?_⟩,
    ⟨((j : ℝ), z0, fun i => G.kMult (trackMate X (e.symm i)).1, z,
      fun i => if b i = true then G.kMult (hFace X L G mk (e.symm i)) else 1, wz), ?_, ?_⟩,
    ⟨fun i => portVec X (e.symm i), u, v, w, fun i => ⟨?_, hu i, hv i, hw i⟩, ?_, fun i => ?_⟩⟩
  -- admissibility
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
  · show longSum X L (trackMate X (e.symm i)).1 ∈ Metric.closedBall 0 (6 * M + 6)
    rw [mem_closedBall_zero_iff]
    linarith [hZ6 _ (hrecv i).1]
  · show (if portB X L G mk (e.symm i) = true then G.kMult (hFace X L G mk (e.symm i)) else 1) ∈
      ({1, 2} : Set ℝ)
    split_ifs
    · exact hkc _
    · simp
  · show (if portB X L G mk (e.symm i) = true then longSum X L (hFace X L G mk (e.symm i))
      else 0) ∈ Metric.closedBall 0 (6 * M + 6)
    rw [mem_closedBall_zero_iff]
    split_ifs with hb
    · linarith [hZ6 _ (hrecvH i hb).1]
    · simp; positivity
  · obtain ⟨hq, hq1, -⟩ := hExtP i
    have hm := hmarg hfm X hX htri L ρ κ G mk lab (labDir lab F0) hmk hκ hζ hρκ hmar _ hq
      (hmat _ hq hq1) hb (hloc' _ hq hq1).1 ((hloc' _ hq hq1).2 hb)
    show min 1 κ ≤ ‖longSum X L (trackMate X (e.symm i)).1‖ ∧
      min 1 κ ≤ ‖longSum X L (trackMate X (e.symm i)).1 +
        (if portB X L G mk (e.symm i) = true then longSum X L (hFace X L G mk (e.symm i))
          else 0)‖
    have hb' : portB X L G mk (e.symm i) = true := hb
    rw [if_pos hb']
    exact hm
  -- the centre
  · refine Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩,
      Finset.mem_product.2 ⟨hz0, Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => hkc' _,
        Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => hz i,
          Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_,
            Fintype.mem_piFinset.2 fun i => hwz i⟩⟩⟩⟩⟩
    by_cases hb : b i = true
    · simp only [hb, if_true]; exact hkc' _
    · simp [hb]
  · refine capDataK_norm_lt hμ0 hjk.symm ?_ rfl (fun i => ?_) rfl (fun i => ?_)
    · show ‖∑ F ∈ Cf, longSum X L F - z0‖ < μ0
      have : ((6 * M : ℕ) : ℝ) * εc = 6 * M * εc := by push_cast; ring
      linarith
    · show ‖longSum X L (trackMate X (e.symm i)).1 - z i‖ < μ0
      linarith [hzd i]
    · show ‖(if portB X L G mk (e.symm i) = true then longSum X L (hFace X L G mk (e.symm i))
        else 0) - wz i‖ < μ0
      linarith [hwzd i]
  -- the approximate solution
  · obtain ⟨hq, -, -⟩ := hExtP i
    obtain ⟨hFg, hsp, -⟩ := mem_unmarkedPorts.1 hq
    obtain ⟨-, hpF, -⟩ := Finset.mem_filter.1 hsp
    obtain ⟨ab, hab, habe⟩ := hside hfm X hX _ _ hpF
    show ‖portVec X (e.symm i)‖ = 1
    rw [portVec_eq (nonempty_of_mem_exceptionalFaces hpF.1) hab habe]
    exact (hfacts hfm X hX G _ hFg).2 ab hab
  · have hmatC : ∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → TrackMated X L G mk q := hmat
    have hsum : ∑ i, portVec X (e.symm i) = ∑ q ∈ extPorts X L G mk Cf, portVec X q := by
      rw [← Finset.sum_coe_sort _ (portVec X)]
      exact Equiv.sum_comp e.symm (fun q => portVec X q)
    have hc := hclo hfm X hX htri L tol G mk lab hmk hlab Cf hCf hmatC
    unfold capRes0K compDataK
    simp only
    rw [hsum]
    have e1 : ((∑ F ∈ Cf, G.kMult F : ℝ) : ℂ) * labDir lab F0 + ∑ F ∈ Cf, longSum X L F +
        ∑ q ∈ extPorts X L G mk Cf, portVec X q =
        (∑ F ∈ Cf, ((G.kMult F : ℂ) * labDir lab F + longSum X L F) +
          ∑ q ∈ (unmarkedPorts X L G mk).filter (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf),
            portVec X q) +
          ∑ F ∈ Cf, (G.kMult F : ℂ) * (labDir lab F0 - labDir lab F) := by
      rw [extPorts]
      push_cast
      rw [Finset.sum_mul, Finset.sum_add_distrib]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e1]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have h2 : ‖∑ F ∈ Cf, (G.kMult F : ℂ) * (labDir lab F0 - labDir lab F)‖ ≤ 2 * Cf.card * ρ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ F ∈ Cf, ‖(G.kMult F : ℂ) * (labDir lab F0 - labDir lab F)‖ ≤ ∑ _F ∈ Cf, 2 * ρ := by
            refine Finset.sum_le_sum fun F hF => ?_
            rw [norm_mul, norm_sub_rev]
            have hk : ‖(G.kMult F : ℂ)‖ ≤ 2 := by
              rcases G.kMult_cases F with h | h <;> rw [h] <;> norm_num
            exact mul_le_mul hk (hloc F hF) (norm_nonneg _) (by norm_num)
        _ = 2 * Cf.card * ρ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hcM : (Cf.card : ℝ) ≤ M := by exact_mod_cast hCM
    have h3 : (Cf.card : ℝ) * tol + 2 * Cf.card * ρ ≤ M * tol + 2 * M * ρ := by
      have := mul_le_mul_of_nonneg_right hcM htol
      have := mul_le_mul_of_nonneg_right hcM hρ0
      nlinarith
    linarith
  · have h := hres i
    unfold capRes1K compDataK
    simp only
    have hbi : b i = portB X L G mk (e.symm i) := rfl
    by_cases hb : portB X L G mk (e.symm i) = true
    · rw [if_pos (hbi ▸ hb), if_pos hb, if_pos hb]
      rw [if_pos hb] at h
      linarith
    · rw [if_neg (hbi ▸ hb)]
      rw [if_neg hb] at h
      linarith

end Erdos99
end

end CaplessKMain

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessKFew`
-/

section CaplessKFew

/-!
# Small capless components of `K` are few (Verification Guide §13.4)

* `stubless_component_factsP`: the faces of a small stubless component of the subgraph on `U`,
  for an arbitrary property `P` of the good faces outside `U`;
* `not_Ks_cases`: a good face outside `K` is a degree-two face or a `J` face;
* `card_badMates_le`: the faces having a matched port into a set `Bad` number at most `4 · #Bad`;
* `capless_K_few`: the stubless components of the subgraph on `K` with at most `M` faces number at
  most `ε D`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim CaplessKElim

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

/-- **The faces of a small stubless component** (general form). -/
lemma stubless_component_factsP (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {U : Finset (Set ℂ)} {P : Set ℂ → Prop}
    (hUP : ∀ F ∈ G.good, F ∉ U → P F)
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
    F0 ∈ Cf ∧ Cf ⊆ U ∧ Cf.card ≤ M ∧
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → TrackMated X L G mk q) ∧
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Cf → P (trackMate X q).1) ∧
      (∀ F ∈ Cf, dist (lab F0).1 (lab F).1 ≤ M * δ) := by
  subst hCfdef
  have hmat : ∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ U.filter (fun x =>
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x = C) →
      TrackMated X L G mk q := fun q hq hqC =>
    mated_of_stubless hstub hq (Finset.mem_filter.1 hqC).1 (Finset.mem_filter.1 hqC).2
  refine ⟨Finset.mem_filter.2 ⟨hF0, hF0C⟩, fun F hF => (Finset.mem_filter.1 hF).1, hsmall,
    hmat, fun q hq hqC hnot => ?_, fun F hF => ?_⟩
  · have hm := hmat q hq hqC
    have hg : (trackMate X q).1 ∈ G.good := (mem_unmarkedPorts.1 hm.2).1
    refine hUP _ hg fun hU' => hnot (Finset.mem_filter.2 ⟨hU', ?_⟩)
    rw [← mate_same_component hends hq hm (Finset.mem_filter.1 hqC).1 hU']
    exact (Finset.mem_filter.1 hqC).2
  · refine component_label_dist lab hδ ?_ hF0 ((hF0C.trans (Finset.mem_filter.1 hF).2.symm)) ?_
    · intro x y hxy
      obtain ⟨-, -, q, hq, hm, he⟩ := cgraph_adj_cases hxy
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hmd q hq hm
      · rw [dist_comm]; exact hmd q hq hm
    · rw [hF0C]; exact hsmall

/-- A good face outside `K` is a degree-two face or a `J` face. -/
lemma not_Ks_cases {F : Set ℂ} (hF : F ∈ G.good) (hK : F ∉ (trackGraph X L G mk).Ks G.good) :
    F ∈ (trackGraph X L G mk).Hs G.good ∨ F ∈ (trackGraph X L G mk).Js G.good := by
  simp only [StubGraph.Ks, StubGraph.Hs, StubGraph.Js, Finset.mem_filter] at hK ⊢
  by_cases h2 : (trackGraph X L G mk).deg F = 2
  · exact Or.inl ⟨hF, h2⟩
  · right
    refine ⟨hF, ?_⟩
    by_contra h
    exact hK ⟨hF, h2, h⟩

lemma Ks_not_Hs {F : Set ℂ} (hK : F ∈ (trackGraph X L G mk).Ks G.good) :
    F ∉ (trackGraph X L G mk).Hs G.good := by
  intro hH
  exact (Finset.mem_filter.1 hK).2.1 (Finset.mem_filter.1 hH).2

/-- The faces having a matched port into `Bad`. -/
def badMates (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (Bad : Finset (Set ℂ)) : Finset (Set ℂ) :=
  ((unmarkedPorts X L G mk).filter (fun q => TrackMated X L G mk q ∧ (trackMate X q).1 ∈ Bad)).image
    Prod.fst

lemma card_badMates_le (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    (hmk : IsMarking X L G mk) (hwin : DegreeWindow X L G) (Bad : Finset (Set ℂ)) :
    (badMates X L G mk Bad).card ≤ 4 * Bad.card := by
  have hM := trackMate_isMatching hends L G mk
  refine Finset.card_image_le.trans ?_
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

/-- **Small capless components of `K` are few** (Verification Guide §13.4, the part `K`).  For
every `M` and `ε, λ > 0` there are a saturation tolerance and a cutoff fraction `a₀` such that for
every cutoff fraction `a ≤ a₀`, eventually every saturated marking with the degree window has at
most `ε D` stubless components of the subgraph on `K` with at most `M` faces. -/
theorem capless_K_few (M : ℕ) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) :
    ∃ tol > 0, ∃ a₀ > 0, ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → IsSaturated X (a * diam X) (lam * diam X) tol G mk →
          ((trackGraph X (a * diam X) G mk).stublessSmall
            ((trackGraph X (a * diam X) G mk).Ks G.good) M : ℝ) ≤ ε * diam X := by
  obtain ⟨Nc, hclus⟩ := long_sides_clustered hlam
  obtain ⟨κ', hκ', cm, hcm, hmarg⟩ := long_side_margin hlam
  set κ : ℝ := κ' / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hε'0 : 0 < ε / (2 * (4 * M + 1)) := by positivity
  choose r hr μ hμ hfew using fun m : ℕ =>
    capless_directions_fewK m (6 * M + 6) (lt_min one_pos hκ : (0 : ℝ) < min 1 κ)
      (capNcentK Nc M m) hε'0
  have hI : (Finset.range (4 * M + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨r0, hr0, hr0m⟩ : ∃ r0 > 0, ∀ m ∈ Finset.range (4 * M + 1), r0 ≤ r m :=
    ⟨_, (Finset.lt_inf'_iff hI).2 fun m _ => hr m, fun m hm => Finset.inf'_le _ hm⟩
  obtain ⟨μ0, hμ0, hμ0m⟩ : ∃ μ0 > 0, ∀ m ∈ Finset.range (4 * M + 1), μ0 ≤ μ m :=
    ⟨_, (Finset.lt_inf'_iff hI).2 fun m _ => hμ m, fun m hm => Finset.inf'_le _ hm⟩
  set ρ : ℝ := min κ (r0 / (4 * M + 8)) with hρdef
  have hρ : 0 < ρ := lt_min hκ (by positivity)
  have hρκ : ρ ≤ κ := min_le_left _ _
  have hρr : ρ ≤ r0 / (4 * M + 8) := min_le_right _ _
  obtain ⟨cρ, hcρ, hclose⟩ := labDir_close hρ
  obtain ⟨εc, hεc, hεcμ⟩ : ∃ εc > 0, εc * (6 * M + 7) = μ0 :=
    ⟨μ0 / (6 * M + 7), by positivity, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨Mb, hclusM⟩ := hclus εc hεc
  obtain ⟨c8, hc8, hc8e⟩ : ∃ c8 > 0, c8 * (8 * (M + 2)) = cρ :=
    ⟨cρ / (8 * (M + 2)), by positivity, div_mul_cancel₀ _ (by positivity)⟩
  set t0 : ℝ := min (min ρ c8) cm with ht0def
  have ht0 : 0 < t0 := lt_min (lt_min hρ hc8) hcm
  have htolρ : t0 ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have htolc : t0 ≤ c8 := (min_le_left _ _).trans (min_le_right _ _)
  have htolm : t0 ≤ cm := min_le_right _ _
  refine ⟨t0, ht0, min c8 cm, lt_min hc8 hcm, fun a ha hab => ?_⟩
  have habc : a ≤ c8 := hab.trans (min_le_left _ _)
  have habm : a ≤ cm := hab.trans (min_le_right _ _)
  filter_upwards [(Filter.eventually_all_finset (Finset.range (4 * M + 1))).2 fun m _ => hfew m,
    hclose, hclusM, component_witnessK, mated_label_dist, card_trackEnds, hmarg,
    eventually_diam_ge (10 * 25 * |Mb| / ε), eventually_diam_ge (2 * (M + 2) / cρ),
    eventually_diam_ge 1] with n hfewn hclosen hclusn hwit hmld hends hmargn hDbig hDbig2 hD1
  intro hfm X hX htri G mk hmk hwin hsat
  have hD : 0 < diam X := lt_of_lt_of_le one_pos (hD1 X hX)
  obtain ⟨hnoint, lab, hlab⟩ := hsat
  obtain ⟨Ucl, hUcl, Bad, hBad, hcl⟩ := hclusn hfm X hX htri
  have hends' := hends hfm X hX htri
  have hmar : ∀ F ∈ G.good, ∀ ab ∈ longSides X (a * diam X) F,
      ((ab.2 - ab.1) * (starRingEnd ℂ) (labDir lab F)).re ≤ 1 / 2 - 2 * κ := by
    intro F hF ab hab
    have := hmargn hfm X hX htri (a * diam X) t0 G mk lab
      (mul_le_mul_of_nonneg_right habm hD.le) htolm hnoint hlab F hF ab hab
    rw [hκdef]; linarith
  -- the parameter inequalities
  have hpar : (M + 2) * (2 * t0 * diam X + 1 + a * diam X) ≤ cρ * diam X := by
    have h1 : 2 * (M + 2) ≤ cρ * diam X := by
      have := hDbig2 X hX
      rw [div_le_iff₀ hcρ] at this; linarith
    have h2 := mul_le_mul_of_nonneg_right htolc hD.le
    have h3 := mul_le_mul_of_nonneg_right habc hD.le
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h4 : (M + 2 : ℝ) * (t0 * diam X) ≤ (M + 2) * (c8 * diam X) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h5 : (M + 2 : ℝ) * (a * diam X) ≤ (M + 2) * (c8 * diam X) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have h6 : (M + 2 : ℝ) * (c8 * diam X) * 8 = cρ * diam X := by rw [← hc8e]; ring
    nlinarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hρr' : ρ * (4 * M + 8) ≤ r0 := by rwa [le_div_iff₀ (by positivity)] at hρr
  have hr1 : M * t0 + 2 * M * ρ < r0 := by
    have := mul_le_mul_of_nonneg_left htolρ hM0
    nlinarith
  have hr2 : 2 * t0 + 4 * ρ < r0 := by nlinarith
  have hμ1 : 6 * M * εc < μ0 := by
    have := mul_nonneg hM0 hεc.le
    nlinarith
  have hL0 : 0 ≤ a * diam X := by positivity
  have hδ0 : 0 ≤ 2 * t0 * diam X + 1 + a * diam X := by positivity
  -- the components
  set U := (trackGraph X (a * diam X) G mk).Ks G.good with hUdef
  have hUgood : U ⊆ G.good := Finset.filter_subset _ _
  have hUP : ∀ F ∈ G.good, F ∉ U → F ∈ (trackGraph X (a * diam X) G mk).Hs G.good ∨
      F ∈ (trackGraph X (a * diam X) G mk).Js G.good := fun F hF hFU => not_Ks_cases hF hFU
  have hmd := hmld hfm X hX htri (a * diam X) t0 G mk lab hlab
  set Bad' := Bad ∪ badMates X (a * diam X) G mk Bad with hBad'
  have hBad'card : Bad'.card ≤ 5 * Bad.card := by
    have := card_badMates_le hends' hmk hwin Bad
    have := Finset.card_union_le Bad (badMates X (a * diam X) G mk Bad)
    rw [hBad']
    omega
  set T := (U.image (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk).filter
    (fun C => (∀ s ∈ (trackGraph X (a * diam X) G mk).S, (trackGraph X (a * diam X) G mk).stub s ∈ U →
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk
        ((trackGraph X (a * diam X) G mk).stub s) ≠ C) ∧
      (U.filter (fun x => (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x
        = C)).card ≤ M) with hTdef
  change (T.card : ℝ) ≤ ε * diam X
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (p := fun C =>
    (∃ F ∈ U, (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad') ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad')
  have hExc := card_excComp_le hends' hmk hwin U Bad' T
  have hrep : ∀ C ∈ T, ∃ F ∈ U,
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F = C :=
    fun C hC => Finset.mem_image.1 (Finset.mem_filter.1 hC).1
  choose! rep hrepU hrepC using hrep
  have hGood := card_le_of_fibres (T.filter (fun C => ¬ ((∃ F ∈ U,
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad') ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad')))
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
        = C ∧ F ∈ Bad') ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad'))).filter (fun C =>
          (extPorts X (a * diam X) G mk (U.filter (fun x =>
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x = C))).card = m)) := by
      intro C hC C' hC' h
      have hCT : C ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 hC).1).1
      have hCT' : C' ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 hC').1).1
      have := hlab.1 (hUgood (hrepU C hCT)) (hUgood (hrepU C' hCT')) h
      rw [← hrepC C hCT, ← hrepC C' hCT', this]
    rw [← Finset.card_image_of_injOn hinj]
    refine hfewn m (Finset.mem_range.2 (by omega)) X hX (capCentresK Ucl M m)
      (card_capCentresK_le hUcl M m) _ ?_ ?_
    · intro p hp
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hp
      have hCT : C ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 hC).1).1
      exact (Finset.mem_filter.1 (hlab.2 _ (hUgood (hrepU C hCT))).1).1
    · intro p hp
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hCG, hfC⟩ := Finset.mem_filter.1 hC
      obtain ⟨hCT, hnexc⟩ := Finset.mem_filter.1 hCG
      obtain ⟨-, hstub, hsmall⟩ := Finset.mem_filter.1 hCT
      obtain ⟨hF0, hCfU, hCM, hmat, hext, hdist⟩ := stubless_component_factsP hends' hUP lab
        hδ0 hmd hstub hsmall (hrepU C hCT) (hrepC C hCT) _ rfl
      set Cf := U.filter (fun x =>
          (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x = C)
        with hCfdef
      have hnB1 : ∀ F ∈ Cf, F ∉ Bad' := fun F hF hFB =>
        hnexc (Or.inl ⟨F, (Finset.mem_filter.1 hF).1, (Finset.mem_filter.1 hF).2, hFB⟩)
      have hnB2 : ∀ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Bad' :=
        fun q hq hqC hB => hnexc (Or.inr ⟨q, hq, (Finset.mem_filter.1 hqC).1,
          (Finset.mem_filter.1 hqC).2, hmat q hq hqC, hB⟩)
      have hnB : ∀ F ∈ Cf, F ∉ Bad := fun F hF hFB => hnB1 F hF (Finset.mem_union_left _ hFB)
      have hnB' : ∀ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Bad :=
        fun q hq hqC hB => hnB2 q hq hqC (Finset.mem_union_left _ hB)
      have hnB'' : ∀ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ Cf →
          portB X (a * diam X) G mk q = true → hFace X (a * diam X) G mk q ∉ Bad := by
        intro q hq hqC hb hB
        have hJ : (trackMate X q).1 ∈ (trackGraph X (a * diam X) G mk).Js G.good := by
          simpa [portB] using hb
        obtain ⟨hsP, hs1, hsm, -⟩ := jSel_spec hends' hJ
        refine hnB2 q hq hqC (Finset.mem_union_right _ ?_)
        refine Finset.mem_image.2 ⟨jSel X (a * diam X) G mk (trackMate X q).1,
          Finset.mem_filter.2 ⟨hsP, hsm, hB⟩, hs1⟩
      have hCfH : ∀ F ∈ Cf, F ∉ (trackGraph X (a * diam X) G mk).Hs G.good :=
        fun F hF => Ks_not_Hs (hCfU hF)
      obtain ⟨bb, d, hd, ⟨c, hc, hdc⟩, ⟨pp, uu, vv, ww, hpu, h0, h1⟩⟩ := hwit hfm X hX htri
        (a * diam X) (lam * diam X) t0 ρ cρ εc μ0 r0 κ M G mk lab Ucl Bad hmk hnoint hlab hcl
        (hclosen X hX) hmar hκ hρκ hpar hr1 hr2 hμ1 hμ0 hεc.le ht0.le hL0 Cf _ hF0
        (hCfU.trans hUgood) hCM hCfH hnB hnB' hnB'' hmat hext hdist
      have hmr : m ∈ Finset.range (4 * M + 1) := Finset.mem_range.2 (by omega)
      subst hfC
      exact ⟨bb, d, hd, ⟨c, hc, hdc.trans_le (hμ0m _ hmr)⟩, pp, uu, vv, ww, hpu,
        h0.trans_le (hr0m _ hmr), fun i => (h1 i).trans_le (hr0m _ hmr)⟩
  have hB1 : (5 * Bad'.card : ℝ) ≤ ε / 2 * diam X := by
    have h1 : (Bad.card : ℝ) ≤ |Mb| := hBad.trans (le_abs_self Mb)
    have h1' : (Bad'.card : ℝ) ≤ 5 * Bad.card := by exact_mod_cast hBad'card
    have h2 := hDbig X hX
    rw [div_le_iff₀ hε] at h2
    linarith
  have hExc' : ((T.filter (fun C => (∃ F ∈ U,
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad') ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad')).card : ℝ) ≤
        5 * Bad'.card := by
    exact_mod_cast hExc
  have hK : ((4 * M : ℕ) + 1 : ℝ) * (ε / (2 * (4 * M + 1)) * diam X) = ε / 2 * diam X := by
    push_cast; field_simp
  rw [← hsplit, Nat.cast_add]
  linarith

end Erdos99
end

end CaplessKFew

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessSmall`
-/

section CaplessSmall

/-!
# Small capless components are pinned (Verification Guide §13.4)

* `capless_small_few`: the local exclusion estimate for `qCapless M`, assembled from
  `capless_G_few` (proved, `CaplessGFew`) and `capless_K_few` (proved, `CaplessKFew`).
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

/-- **Small capless components of `G` and `K` are pinned** (Verification Guide §13.4). -/
theorem capless_small_few (η : ℝ) (_hη : 0 < η) (M : ℕ) : LocalExclusion η (qCapless M) := by
  intro ε hε lam hlam θ δ _ _
  obtain ⟨t1, ht1, b1, hb1, h1⟩ := capless_G_few M (ε := ε / 2) (by positivity) hlam
  obtain ⟨t2, ht2, b2, hb2, h2⟩ := capless_K_few M (ε := ε / 2) (by positivity) hlam
  refine ⟨min t1 t2, lt_min ht1 ht2, min b1 b2, lt_min hb1 hb2, fun a ha hab => ?_⟩
  filter_upwards [h1 a ha (hab.trans (min_le_left _ _)), h2 a ha (hab.trans (min_le_right _ _)),
    eventually_diam_ge 0] with n e1 e2 hD
  intro hfm X hX htri O _ G mk hmk hwin hsat
  have q1 := e1 hfm X hX htri G mk hmk hwin (hsat.mono_tol (min_le_left _ _) (hD X hX))
  have q2 := e2 hfm X hX htri G mk hmk hwin (hsat.mono_tol (min_le_right _ _) (hD X hX))
  simp only [qCapless]
  linarith

end Erdos99
end

end CaplessSmall

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `UnflaggedMargin`
-/

section UnflaggedMargin

/-!
# The unflagged margin (Verification Guide §§6, 12.4, 13.2–13.3)

The local exclusion estimates `defective_J_few` (§13.2) and `exceptional_JJ_few` (§13.3) need the
following margin: every *retained* port vector `z` of an *unflagged* good face (a side of the face
whose track has at least `L` rhombi) satisfies `z · τ < -θ`, where `τ` is the unit tangent of the
source label of the face.  This file proves this margin from two-sided roundness and saturation.

* `IsRoundCentre ρ X O`: `O` is the centre supplied by the two-sided roundness theorem
  (`RoundData X O D η δ` with `δ ≤ ρ`: `X` lies in the disc of radius `D/2 + η D` about `O` and
  reaches `D/2 - δ D` in every direction; recall `η ≤ δ`).  `eventually_isRoundCentre`: for every
  `ρ > 0`, eventually every optimal configuration has such a centre (from `eventually_roundData`).
* `port_radial_band` (**the radial-band predicate**): a side `(a, b)` of a face whose vertices lie
  within `tol · D` of the start of a counterclockwise hull side `p` (boundary localization of a
  good face, part of `IsLabelled`) has its midpoint within `(√(3δ) + tol) D + 1/2` of the circle
  point `O + (D/2) ν_p`, `ν_p = -J τ_p` the outward normal of `p`.  With `√(3δ) + tol ≤ δ_flag / 2`
  and `D ≥ 1 / δ_flag` this is inside the flag band `δ_flag D`.
* `port_track_side`: the track through a side `(a, b)` of an exceptional face (with rhombi) lies on
  the side `n = -J (b - a)` of it (away from the face).
* `unflagged_port_margin`: hence, for a good face `F` that is not flagged, every side `(a, b)` of
  `F` on a track with at least `L > 0` rhombi (and so, by saturation, at least `λ D`) whose
  midpoint is in the flag band about `O + (D/2) ν` satisfies `n · ν < -θ`; with `ν = -J τ` this is
  `(b - a) · τ < -θ`.
* `HasUnflaggedMargin`: source labels as in `IsLabelled` together with this margin for the unflagged
  faces; `saturated_unflagged_margin` proves it at the call sites from `RoundData` and
  `IsSaturated`, for the maximal flagged set `flaggedFaces`.
* `margin_transfer`, `unflagged_margin_transfer`: if the face tangent and a common pattern
  tangent differ by at most `θ / 2`, the projection on the common tangent stays below `-θ/2`; by
  tangent regularity (`sideDir_sub_le`) this holds for labels starting at distance `s` with
  `2 s / D + 4 √(3δ) ≤ θ / 2`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## The centre of two-sided roundness -/

/-- `O` is a centre of two-sided roundness with inner defect at most `ρ`: for some `η ≤ δ ≤ ρ`,
`X` lies in the disc of radius `D/2 + η D` about `O` and reaches `D/2 - δ D` in every direction
(`RoundData`). -/
def IsRoundCentre (ρ : ℝ) (X : Finset Plane) (O : Plane) : Prop :=
  ∃ ηr δr : ℝ, RoundData X O (diam X) ηr δr ∧ δr ≤ ρ

lemma IsRoundCentre.mono {ρ ρ' : ℝ} {X : Finset Plane} {O : Plane} (h : IsRoundCentre ρ X O)
    (hρ : ρ ≤ ρ') : IsRoundCentre ρ' X O := by
  obtain ⟨ηr, δr, hR, hδ⟩ := h
  exact ⟨ηr, δr, hR, hδ.trans hρ⟩

/-- A centre of two-sided roundness with defect `ρ` is the centre of a disc of radius
`D/2 + ρ D` containing `X`. -/
lemma IsRoundCentre.ball {ρ : ℝ} {X : Finset Plane} {O : Plane} (h : IsRoundCentre ρ X O) :
    ∀ x ∈ X, dist x O ≤ diam X / 2 + ρ * diam X := by
  obtain ⟨ηr, δr, hR, hδ⟩ := h
  intro x hx
  have h1 := hR.ball x hx
  have h2 : ηr * diam X ≤ ρ * diam X :=
    mul_le_mul_of_nonneg_right (hR.η_le.trans hδ) hR.D_pos.le
  linarith

/-- **Two-sided roundness** (Lemma 3.1 with the inner half, `eventually_roundData`): for every
`ρ > 0`, eventually every optimal configuration has a centre of two-sided roundness with defect at
most `ρ`. -/
theorem eventually_isRoundCentre (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X → ∃ O, IsRoundCentre ρ X O := by
  filter_upwards [eventually_roundData ρ hρ] with n h X hX
  obtain ⟨O, ηr, δr, hR, hδ⟩ := h X hX
  exact ⟨O, ηr, δr, hR, hδ⟩

/-- **The counting data from the track count at centres of two-sided roundness.**  The form of
`exists_countingWitness_of` in which the track count is only required at centres of two-sided
roundness, with a defect `ρ` chosen after `ε, η`; the centres are supplied by
`eventually_isRoundCentre`. -/
lemma exists_countingWitness_of_round
    (htc : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
        ∃ L : ℝ, 0 ≤ L ∧ L ≤ ε * diam X ∧ ∃ sel ⊆ longTracks X L,
          (∀ T ∈ sel, IsSelectedTrack O (diam X) η T) ∧
          ((longTracks X L).card : ℝ) - sel.card ≤ 3 / 5 * (π * diam X - sel.card) + ε * diam X)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      Nonempty (CountingWitness X ε) :=
  exists_countingWitness_of_centre IsRoundCentre
    (fun η ρ hη hρ => by
      filter_upwards [eventually_isRoundCentre (min η ρ) (lt_min hη hρ)] with n h X hX
      obtain ⟨O, hO⟩ := h X hX
      refine ⟨O, fun x hx => ?_, hO.mono (min_le_right _ _)⟩
      have h1 := hO.ball x hx
      have h2 : min η ρ * diam X ≤ η * diam X :=
        mul_le_mul_of_nonneg_right (min_le_left _ _)
          (by obtain ⟨_, _, hR, _⟩ := hO; exact hR.D_pos.le)
      linarith)
    htc ε hε

/-! ## Small geometric facts -/

lemma inner_rot_rot_plane (x y : Plane) : inner ℝ (rot x) (rot y) = inner ℝ x y := by
  rw [inner_coord, inner_coord]; simp [rot]; ring

lemma rot_sub_plane (x y : Plane) : rot (x - y) = rot x - rot y := by
  ext i; fin_cases i <;> simp [rot]; ring

lemma norm_mid_sub_left {a b : Plane} (hab : dist a b = 1) : ‖mid s(a, b) - a‖ = 1 / 2 := by
  rw [mid_mk]
  have : (1 / 2 : ℝ) • (a + b) - a = (1 / 2 : ℝ) • (b - a) := by
    rw [smul_sub, smul_add]; module
  rw [this, norm_smul, ← dist_eq_norm, dist_comm, hab]; norm_num

/-! ## The radial-band predicate -/

/-- **The radial-band predicate for the ports of a localized face.**  Let `p` be a
counterclockwise hull side of a round configuration (`RoundData X O D η δ`), with outward normal
`ν_p = -J τ_p`.  A unit side `(a, b)` whose start lies within `tol · D` of the start of `p` (the
boundary localization of a good face with label `p`) has its midpoint within
`(√(3δ) + tol) D + 1/2` of the circle point `O + (D/2) ν_p`. -/
theorem port_radial_band {X : Finset Plane} {O : Plane} {D ηr δr : ℝ}
    (hR : RoundData X O D ηr δr) {p : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2)
    {a b : Plane} (hab : dist a b = 1) {tol : ℝ} (ha : ‖a - p.1‖ ≤ tol * D) :
    ‖mid s(a, b) - O - (D / 2) • (-rot (sideDir p))‖ ≤ (√(3 * δr) + tol) * D + 1 / 2 := by
  have h1 := side_normal_near hR hp
  have h2 := norm_mid_sub_left hab
  have e : mid s(a, b) - O - (D / 2) • (-rot (sideDir p)) =
      (mid s(a, b) - a) + (a - p.1) + (p.1 - O - (D / 2) • (-rot (sideDir p))) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le (mid s(a, b) - a) (a - p.1)
  nlinarith

/-- The radial band fits inside the flag band of width `δ D` once `√(3δ_r) + tol ≤ δ / 2` and
`D ≥ 1 / δ`. -/
lemma radial_band_le_flag {δr tol δ D : ℝ} (hsmall : √(3 * δr) + tol ≤ δ / 2)
    (hD : 1 ≤ δ * D) (hD0 : 0 ≤ D) : (√(3 * δr) + tol) * D + 1 / 2 ≤ δ * D := by
  have := mul_le_mul_of_nonneg_right hsmall hD0
  nlinarith

/-! ## The track through a face side lies away from the face -/

/-- **The track through a side of an exceptional face lies on the far side.**  If `(a, b)` is an
oriented side of an exceptional face `F` (face on the left) and lies on a rhombus, then every edge
`f` of its track satisfies `(m_f - m_e) · n ≥ 0` for the outward normal `n = -J (b - a)`. -/
theorem port_track_side {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {F : Set ℂ} (hF : F ∈ exceptionalFaces X) {a b : Plane}
    (hab : (toC a, toC b) ∈ orientedSides X F) (heR : s(a, b) ∈ rhombusEdges X) :
    ∀ f ∈ trackOf X s(a, b), 0 ≤ inner ℝ (mid f - mid s(a, b)) (-rot (b - a)) := by
  obtain ⟨u, -, hdir, hmin⟩ :=
    exists_orientation hX htri heR (isTerminal_of_mem_orientedSides hX htri hF hab)
  have hht : ∀ f ∈ trackOf X s(a, b), 0 ≤ inner ℝ (mid f - mid s(a, b)) (rot u) := by
    intro f hf
    have := hmin f hf
    simp only [ht] at this
    rw [inner_sub_left]; linarith
  have hu : rot u = -rot (b - a) ∨ rot u = rot (b - a) := by
    have hd := hdir _ (mem_trackOf_self heR)
    have hab' : rot (a - b) = -rot (b - a) := by
      rw [← rot_neg, neg_sub]
    rcases dv_mk a b with h | h <;> rcases hd with h' | h'
    · left; rw [← h', h, hab']
    · right; have : u = b - a := by rw [← neg_neg u, ← h', h, neg_sub]
      rw [this]
    · right; rw [← h', h]
    · left; have : u = a - b := by rw [← neg_neg u, ← h', h, neg_sub]
      rw [this, hab']
  rcases hu with hu | hu
  · rw [← hu]; exact hht
  · exfalso
    obtain ⟨f1, o⟩ := (Finset.mem_filter.1 heR).2
    obtain ⟨q, hq | hq, hqf⟩ := leftStep_of_oppositeSides hX htri o
    · exact initial_of_mem_orientedSides hX htri hF hab ⟨_, hq.rev⟩
    · have hf1 : f1 ∈ trackOf X s(a, b) :=
        mem_trackOf.2 ⟨mem_rhombusEdges_of_opp (oppositeSides_symm o), Relation.EqvGen.rel _ _ o⟩
      have h0 := hht f1 hf1
      rw [hu, ← hqf] at h0
      obtain ⟨-, -, -, -, -, hpar, hdet⟩ := hq
      simp only at hpar hdet
      have hm : mid s(q.1, q.2) - mid s(a, b) = q.1 - b := by
        rw [mid_mk, mid_mk]
        have : q.2 = q.1 + (a - b) := by rw [← hpar]; abel
        rw [this]; module
      rw [hm, inner_rot_eq_det2] at h0
      have : det2 (b - a) (q.1 - b) = -det2 (a - b) (q.1 - b) := by unfold det2; simp; ring
      linarith

/-! ## Unflagged faces have the margin -/

/-- **Unflagged ports have the margin.**  Let `F` be a good face that is not flagged (for the
cutoff `L > 0`, the macroscopic fraction `λ` and the tolerances `θ, δ`).  Let `(a, b)` be an
oriented side of `F` which is a port of `F` on a track with at least `L` rhombi and at least `λ D`
rhombi, and whose midpoint lies within `δ D` of the circle point `O + (D/2) ν` (`ν` a unit vector).
Then `n · ν < -θ` for the outward normal `n = -J (b - a)`. -/
theorem unflagged_port_margin {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {O : Plane} {L lam θ δ : ℝ} {G : GoodFaces X} {F : Set ℂ} (hF : F ∈ G.good)
    (hnf : F ∉ flaggedFaces X O L lam θ δ G) {a b : Plane}
    (hab : (toC a, toC b) ∈ orientedSides X F) (hport : IsPort X (Sum.inl F) s(a, b))
    (hL : 0 < L) (hlen : L ≤ trackLength X (allTrackOf X s(a, b)))
    (hlam : lam * diam X ≤ trackLength X (allTrackOf X s(a, b))) {ν : Plane} (hν : ‖ν‖ = 1)
    (hband : ‖mid s(a, b) - O - (diam X / 2) • ν‖ ≤ δ * diam X) :
    inner ℝ (-rot (b - a)) ν < -θ := by
  have hFe : F ∈ exceptionalFaces X :=
    (mem_exceptionalFinset hX).1 (G.good_subset hF)
  have heu : s(a, b) ∈ unitEdges X := by
    rw [Sym2.eq_swap]; exact mem_unitEdges_of_mem_orientedSides hab
  have heR : s(a, b) ∈ rhombusEdges X := by
    by_contra h
    rw [allTrackOf_of_not_mem heu h, trackLength_singleton hX htri heu h] at hlen
    norm_num at hlen; linarith
  rw [allTrackOf_of_mem_rhombusEdges heR] at hlen hlam
  by_contra hcon
  push_neg at hcon
  apply hnf
  refine Finset.mem_filter.2 ⟨hF, trackOf X s(a, b), ?_, hlam, s(a, b), mem_trackOf_self heR,
    hport, ν, -rot (b - a), hν, ?_, hband, hcon, port_track_side hX htri hFe hab heR⟩
  · exact Finset.mem_filter.2 ⟨trackOf_mem_tracks heR, hlen⟩
  · rcases dv_mk a b with h | h
    · left; rw [h, ← rot_neg, neg_sub]
    · right; rw [h]

/-- With `ν = -J τ` the margin reads `(b - a) · τ < -θ`. -/
lemma inner_neg_rot_neg_rot (z τ : Plane) : inner ℝ (-rot z) (-rot τ) = inner ℝ z τ := by
  rw [inner_neg_left, inner_neg_right, neg_neg, inner_rot_rot_plane]

/-! ## Source labels with the unflagged margin -/

/-- **Source labels with the unflagged margin**: source labels as in `IsLabelled` (unit hull sides,
injective, marked sum `≈ k τ` within `tol`, boundary localization within `tol · D`), such that
every good face outside `Fl` has the margin: each of its oriented sides `(a, b)` that is a port on a
track with at least `L` rhombi (a *retained* port) satisfies `(b - a) · τ < -θ`, where `τ` is the
unit direction of its label. -/
def HasUnflaggedMargin (X : Finset Plane) (L θ tol : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) (Fl : Finset (Set ℂ)) : Prop :=
  ∃ lab : Set ℂ → Plane × Plane, Set.InjOn lab G.good ∧ ∀ F ∈ G.good,
    lab F ∈ unitHullSides X ∧
    ‖markedSum X F (mk F) - G.markMult F * toC (sideDir (lab F))‖ ≤ tol ∧
    (∀ ab ∈ orientedSides X F, ‖ab.1 - toC (lab F).1‖ ≤ tol * diam X) ∧
    (F ∉ Fl → ∀ ab ∈ orientedSides X F, ∀ e ∈ unitEdges X, IsPort X (Sum.inl F) e →
      Sym2.map toC e = s(ab.1, ab.2) → L ≤ trackLength X (allTrackOf X e) →
      inner ℝ (ab.2 - ab.1) (toC (sideDir (lab F))) < -θ)

lemma HasUnflaggedMargin.mono_tol {X : Finset Plane} {L θ tol tol' : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {Fl : Finset (Set ℂ)} (h : HasUnflaggedMargin X L θ tol G mk Fl)
    (ht : tol ≤ tol') (hD : 0 ≤ diam X) : HasUnflaggedMargin X L θ tol' G mk Fl := by
  obtain ⟨lab, hinj, hl⟩ := h
  refine ⟨lab, hinj, fun F hF => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hl F hF
  exact ⟨h1, h2.trans ht, fun ab hab => (h3 ab hab).trans (mul_le_mul_of_nonneg_right ht hD), h4⟩

lemma HasUnflaggedMargin.isLabelled {X : Finset Plane} {L θ tol : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {Fl : Finset (Set ℂ)}
    (h : HasUnflaggedMargin X L θ tol G mk Fl) : IsLabelled X tol G mk := by
  obtain ⟨lab, hinj, hl⟩ := h
  exact ⟨lab, hinj, fun F hF => ⟨(hl F hF).1, (hl F hF).2.1, (hl F hF).2.2.1⟩⟩

/-- **The unflagged margin at the call sites.**  Eventually: for a round configuration
(`RoundData X O D η δ_r`) and saturated good faces (`IsSaturated` at the cutoff `L > 0`, the
macroscopic scale `λ D` and tolerance `tol`), if the radial band `(√(3δ_r) + tol) D + 1/2` is
within the flag band `δ D`, then the source labels of the saturation have the unflagged margin for
the maximal flagged set `flaggedFaces X O L λ θ δ G`. -/
theorem saturated_unflagged_margin :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (O : Plane) (ηr δr : ℝ), RoundData X O (diam X) ηr δr →
      ∀ (L lam θ δ tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), 0 < L →
        IsSaturated X L (lam * diam X) tol G mk →
        (√(3 * δr) + tol) * diam X + 1 / 2 ≤ δ * diam X →
        HasUnflaggedMargin X L θ tol G mk (flaggedFaces X O L lam θ δ G) := by
  filter_upwards [exists_side_of_port] with n hside hfm X hX htri O ηr δr hR L lam θ δ tol G mk
    hL hsat hband
  have hsep : IsSeparated X := hX.1.2
  obtain ⟨hnoint, lab, hinj, hl⟩ := hsat
  refine ⟨lab, hinj, fun F hF => ⟨(hl F hF).1, (hl F hF).2.1, (hl F hF).2.2, ?_⟩⟩
  intro hnf ab hab e he hpe hmap hlen
  obtain ⟨hlabU, -, hloc⟩ := hl F hF
  have hp : IsCcwHullSide X (lab F).1 (lab F).2 :=
    (Finset.mem_filter.1 (Finset.mem_filter.1 hlabU).1).2
  -- write the side in coordinates of the plane
  set a := toC.symm ab.1 with ha
  set b := toC.symm ab.2 with hb
  have hab' : (toC a, toC b) ∈ orientedSides X F := by
    simp only [ha, hb, LinearIsometryEquiv.apply_symm_apply]; exact hab
  have he' : e = s(a, b) := by
    have h1 : Sym2.map toC e = Sym2.map toC s(a, b) := by
      rw [hmap]; simp [ha, hb, Sym2.map_mk]
    exact Sym2.map.injective toC.injective h1
  subst he'
  have hdist : dist a b = 1 := dist_eq_one_of_mem_orientedSides hab'
  have hloc' : ‖a - (lab F).1‖ ≤ tol * diam X := by
    have := hloc ab hab
    rwa [show ab.1 = toC a by simp [ha], ← map_sub, LinearIsometryEquiv.norm_map] at this
  have hlam : lam * diam X ≤ trackLength X (allTrackOf X s(a, b)) :=
    (hnoint F hF _ he hpe).resolve_left (not_lt.2 hlen)
  have hν : ‖-rot (sideDir (lab F))‖ = 1 := by
    rw [norm_neg, norm_rot, norm_sideDir hp.2.2.1]
  have hb' := (port_radial_band hR hp hdist hloc').trans hband
  have key := unflagged_port_margin hsep htri hF hnf hab' hpe hL hlen hlam hν hb'
  rw [inner_neg_rot_neg_rot] at key
  rwa [show ab.2 - ab.1 = toC b - toC a by simp [ha, hb], ← map_sub,
    LinearIsometryEquiv.inner_map_map]

/-! ## Transfer to a common pattern tangent -/

/-- **Margin transfer.**  If a unit vector `z` has projection `< -θ` on `τ`, and `τ₀` is within
`θ / 2` of `τ`, then `z` has projection `< -θ/2` on `τ₀`. -/
lemma margin_transfer {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {z τ τ₀ : E}
    (hz : ‖z‖ = 1) {θ : ℝ} (h : inner ℝ z τ < -θ) (hτ : ‖τ - τ₀‖ ≤ θ / 2) :
    inner ℝ z τ₀ < -θ / 2 := by
  have e : inner ℝ z τ₀ = inner ℝ z τ - inner ℝ z (τ - τ₀) := by
    rw [inner_sub_right]; ring
  have h1 : inner ℝ z (τ - τ₀) ≥ -‖τ - τ₀‖ := by
    have := abs_real_inner_le_norm z (τ - τ₀)
    rw [hz, one_mul] at this
    linarith [neg_abs_le (inner ℝ z (τ - τ₀))]
  linarith

/-- **Transfer of the unflagged margin to a common pattern tangent.**  If the label tangent of an
unflagged good face is within `θ / 2` of a common tangent `τ₀`, its retained ports have projection
`< -θ/2` on `τ₀`. -/
lemma unflagged_margin_transfer {X : Finset Plane} {L θ : ℝ} {Fl : Finset (Set ℂ)}
    {lab : Set ℂ → Plane × Plane} {F : Set ℂ}
    (hmar : F ∉ Fl → ∀ ab ∈ orientedSides X F, ∀ e ∈ unitEdges X, IsPort X (Sum.inl F) e →
      Sym2.map toC e = s(ab.1, ab.2) → L ≤ trackLength X (allTrackOf X e) →
      inner ℝ (ab.2 - ab.1) (toC (sideDir (lab F))) < -θ)
    (hnf : F ∉ Fl) {τ₀ : ℂ} (hτ : ‖toC (sideDir (lab F)) - τ₀‖ ≤ θ / 2)
    {ab : ℂ × ℂ} (hab : ab ∈ orientedSides X F) (hunit : ‖ab.2 - ab.1‖ = 1)
    {e : Sym2 Plane} (he : e ∈ unitEdges X) (hpe : IsPort X (Sum.inl F) e)
    (hmap : Sym2.map toC e = s(ab.1, ab.2)) (hlen : L ≤ trackLength X (allTrackOf X e)) :
    inner ℝ (ab.2 - ab.1) τ₀ < -θ / 2 :=
  margin_transfer hunit (hmar hnf ab hab e he hpe hmap hlen) hτ

/-- **Tangent regularity for labels** (from `sideDir_sub_le`): two counterclockwise hull sides of a
round configuration starting at distance `s` have tangents within `θ / 2` once
`2 s / D + 4 √(3δ) ≤ θ / 2`. -/
lemma label_tangent_close {X : Finset Plane} {O : Plane} {D ηr δr : ℝ}
    (hR : RoundData X O D ηr δr) {p q : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2)
    (hq : IsCcwHullSide X q.1 q.2) {θ : ℝ} (hsmall : 2 * dist p.1 q.1 / D + 4 * √(3 * δr) ≤ θ / 2) :
    ‖toC (sideDir p) - toC (sideDir q)‖ ≤ θ / 2 := by
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  exact (sideDir_sub_le hR hp hq).trans hsmall

end Erdos99

end

end UnflaggedMargin

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FlaggedPoly`
-/

section FlaggedPoly

/-!
# The eliminated polynomials of §§13.2–13.3 are not zero

The relations of §13.2 (an unflagged `J` face with two unflagged `H` neighbours) and of §13.3
(adjacent unflagged `J` faces, each with an unflagged `H` neighbour) have the shape of the
relations of a capless `K` component (`capless_solutions_card_leK`) with `k₀ = 0`, `Z₀ = 0` and two
outgoing ports:

* §13.2: `p₀ = -s₂` is the two-stage response of the `J` face over its first `H` neighbour, and
  `p₁ = s₂` is the response of the second `H` neighbour; `p₀ + p₁ = 0`;
* §13.3: `p₀ = -t` is the two-stage response of the first `J` face and `p₁ = t` the one of the
  second `J` face (`t` the side vector of the track joining them); `p₀ + p₁ = 0`.

Since `k₀ = 0`, the nonvanishing argument of §13.4 does not apply.  Instead:

* `defJ_elim_ne_zero` (§13.2): a common root gives the unit condition `a a⋆ = 1` for
  `a = l T + v + s₁ + s₂`, `a⋆ = l / T + conj v + s₁⁻¹ + s₂⁻¹` (`jQuad_neg_eq`); for large `T`,
  `Re (a / T) ≥ 1/2` and `a⋆` is close to `conj (v + e₁ + e₂)` with `eᵢ ∈ {0, Wᵢ}`, whose norm is
  bounded below by the margin; so `‖a a⋆‖` is large.
* `jj_elim_ne_zero` (§13.3): a common root gives identity (H1) for `aᵢ = lᵢ T + Zᵢ + vᵢ`,
  `aᵢ⋆ = lᵢ / T + conj Zᵢ + vᵢ⁻¹` (`res22_hh`); its cubic part
  `a₁ a₂ (a₁ + a₂) a₁⋆ a₂⋆ (a₁⋆ + a₂⋆)` dominates the squared term for large `T`.
* `solutions_card_le_of_ne`: the uniform bound on the exact solutions, given nonvanishing.
-/

open Polynomial Filter ComplexConjugate

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessKElim

open CaplessElim

/-- **Few exact solutions, given that the eliminated polynomial is not zero.** -/
theorem solutions_card_le_of_ne (k0 : ℝ) (Z0 : ℂ) (b : ℕ → Bool) (k : ℕ → ℝ)
    (Z : ℕ → ℂ) (k2 : ℕ → ℝ) (W : ℕ → ℂ) (m : ℕ)
    (hne : elimQK (k0 : ℂ) Z0 (kq b k Z k2 W) m ≠ 0) :
    ∃ S : Finset ℂ, S.card ≤ capDegK m ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : ℕ → ℂ,
      (∀ i < m, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1 ∧
        (if b i then (k i : ℂ) * ζ + Z i - p i + v i + u i = 0 ∧
            (k2 i : ℂ) * ζ + W i - v i + w i = 0
          else (k i : ℂ) * ζ + Z i - p i + u i = 0)) →
      (k0 : ℂ) * ζ + Z0 + ∑ i ∈ Finset.range m, p i = 0 → ζ ∈ S := by
  set Q := elimQK (k0 : ℂ) Z0 (kq b k Z k2 W) m
  refine ⟨Q.roots.toFinset, (Multiset.toFinset_card_le _).trans
    ((card_roots' Q).trans (natDegree_elimQK_le _ _ b _ _ _ _ _ _ m)),
    fun ζ hζ p u v w hpu hsum => ?_⟩
  rw [Multiset.mem_toFinset, mem_roots hne]
  show ((elimPK (kq b k Z k2 W) m).eval (respA (k0 : ℂ) Z0)).eval ζ = 0
  rw [eval_eval_eq_eval_map]
  refine elimPK_eval_eq_zero _ (fun _ => natDegree_qK_le _ _ _ _ _ _ _) ζ p m (fun i hi => ?_) _ ?_
  · obtain ⟨hp, hu, hv, hw, he⟩ := hpu i hi
    cases hb : b i
    · rw [hb] at he
      simp only [Bool.false_eq_true, if_false] at he
      simp only [qK, Bool.false_eq_true, if_false, Polynomial.map_pow, eval_pow]
      have hpa : ‖p i - ((k i : ℝ) * ζ + Z i)‖ = 1 := by
        rw [show p i - ((k i : ℝ) * ζ + Z i) = u i by linear_combination -he, hu]
      have := QuadraticResponse.two_circle_eq_poly (k i) hζ hp hpa
      rw [respQ_map_eval, pow_eq_zero_iff two_ne_zero]
      linear_combination this
    · rw [hb] at he
      simp only [if_true] at he
      simp only [qK, if_true]
      have hva : ‖v i - ((k2 i : ℝ) * ζ + W i)‖ = 1 := by
        rw [show v i - ((k2 i : ℝ) * ζ + W i) = w i by linear_combination -he.2, hw]
      have hH := QuadraticResponse.two_circle_eq_poly (k2 i) hζ hv hva
      have hpa : ‖p i - ((k i : ℝ) * ζ + (Z i + v i))‖ = 1 := by
        rw [show p i - ((k i : ℝ) * ζ + (Z i + v i)) = u i by linear_combination -he.1, hu]
      refine jQuartic_eval_eq_zero (v := v i) ?_ (jQuad_of_unit hζ hv hp hpa)
      rw [hQuad]
      linear_combination hH
  · simpa [respA] using hsum

/-! ## Algebraic identities -/

/-- The `J` quadratic at `-p` is the unit condition `a a⋆ = 1` (§13.2). -/
lemma jQuad_neg_eq {l : ℝ} {Z T v p : ℂ} (hT : T ≠ 0) (hv : v ≠ 0) (hp : p ≠ 0) :
    jQuad l Z T v (-p) = T * v * p * (((l : ℂ) * T + Z + v + p) *
      ((l : ℂ) / T + conj Z + v⁻¹ + p⁻¹) - 1) := by
  unfold jQuad; field_simp; ring

/-- The `J` quadratic, normalised. -/
lemma jQuad_eq_mul {l : ℝ} {Z T v p : ℂ} (hT : T ≠ 0) (hv : v ≠ 0) :
    jQuad l Z T v p = T * v * (((l : ℂ) / T + conj Z + v⁻¹) * p ^ 2 +
      (-(((l : ℂ) * T + Z + v) * ((l : ℂ) / T + conj Z + v⁻¹))) * p + ((l : ℂ) * T + Z + v)) := by
  unfold jQuad; field_simp; ring

/-- The resultant of the two normalised `J` quadratics of §13.3 is the (H1) expression. -/
lemma res22_hh (a aS b bS : ℂ) :
    res22 aS (a * aS) a bS (-(b * bS)) b = QuadraticResponse.hhExpr a aS b bS := by
  unfold res22 QuadraticResponse.hhExpr; ring

lemma inv_near_choice {v W : ℂ} {ε : ℝ} (h : ‖v⁻¹‖ ≤ ε ∨ ‖v⁻¹ - conj W‖ ≤ ε) :
    ∃ e : ℂ, (e = 0 ∨ e = W) ∧ ‖v⁻¹ - conj e‖ ≤ ε := by
  rcases h with h | h
  · exact ⟨0, Or.inl rfl, by simpa using h⟩
  · exact ⟨W, Or.inr rfl, h⟩

lemma norm_real_div_le {x T : ℝ} (hx : 0 ≤ x) (hT : 0 < T) : ‖((x : ℂ) / (T : ℂ))‖ = x / T := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hx,
    Real.norm_of_nonneg hT.le]

/-- The real part of `(l T + Z + y₁ + y₂) / T` for large `T`. -/
lemma re_lead2 {l T : ℝ} (hl : 1 ≤ l) (hT : 0 < T) {Z y1 y2 : ℂ} (hZ : 8 * ‖Z‖ ≤ T) {ε : ℝ}
    (hε : ε ≤ 1 / 8) (h1 : -ε ≤ (y1 / T).re) (h2 : -ε ≤ (y2 / T).re) :
    1 / 2 ≤ (((l : ℂ) * T + Z + y1 + y2) / T).re := by
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have e : ((l : ℂ) * T + Z + y1 + y2) / T = l + Z / T + y1 / T + y2 / T := by
    field_simp
  rw [e, Complex.add_re, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  have h3 := re_ge_neg_norm (Z / T)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT.le] at h3
  have h4 : ‖Z‖ / T ≤ 1 / 8 := by rw [div_le_iff₀ hT]; linarith
  linarith

lemma norm_ge_of_re_div {a : ℂ} {T : ℝ} (hT : 0 < T) (h : 1 / 2 ≤ (a / T).re) : T / 2 ≤ ‖a‖ := by
  have h1 := Complex.re_le_norm (a / T)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT.le, le_div_iff₀ hT] at h1
  nlinarith

/-! ## §13.2 -/

/-- Port types of §13.2: a two-stage `J` response, then an `H` response. -/
def djB : ℕ → Bool := fun i => decide (i = 0)

/-- The multiplicities of §13.2. -/
def djK (l k2 : ℝ) : ℕ → ℝ := fun i => if i = 0 then l else k2

/-- The retained sums of §13.2. -/
def djZ (v W2 : ℂ) : ℕ → ℂ := fun i => if i = 0 then v else W2

/-- The response polynomials of §13.2. -/
def djq (l k1 k2 : ℝ) (v W1 W2 : ℂ) : ℕ → ℂ[X][X] :=
  kq djB (djK l k2) (djZ v W2) (fun _ => k1) (fun _ => W1)

lemma djq_zero (l k1 k2 : ℝ) (v W1 W2 : ℂ) :
    djq l k1 k2 v W1 W2 0 = jQuartic (l : ℂ) v (conj v) (k1 : ℂ) W1 (conj W1) := by
  simp [djq, kq, djB, djK, djZ, qK]

lemma djq_one (l k1 k2 : ℝ) (v W1 W2 : ℂ) :
    djq l k1 k2 v W1 W2 1 = respQ (k2 : ℂ) W2 (conj W2) ^ 2 := by
  simp [djq, kq, djB, djK, djZ, qK]

/-- **The eliminated polynomial of §13.2 is not zero**, under the margin
`‖v + e₁ + e₂‖ ≥ c > 0` for `e₁ ∈ {0, W₁}`, `e₂ ∈ {0, W₂}`. -/
theorem defJ_elim_ne_zero {l k1 k2 : ℝ} (hl : l = 1 ∨ l = 2) (hk1 : k1 = 1 ∨ k1 = 2)
    (hk2 : k2 = 1 ∨ k2 = 2) {v W1 W2 : ℂ} {c : ℝ} (hc : 0 < c)
    (hmar : ∀ e1 e2 : ℂ, (e1 = 0 ∨ e1 = W1) → (e2 = 0 ∨ e2 = W2) → c ≤ ‖v + e1 + e2‖) :
    elimQK ((0 : ℝ) : ℂ) 0 (djq l k1 k2 v W1 W2) 2 ≠ 0 := by
  intro hQ
  have hv0 : v ≠ 0 := by
    intro h; have := hmar 0 0 (Or.inl rfl) (Or.inl rfl); rw [h] at this; simp at this; linarith
  have hvW : v + W1 ≠ 0 := by
    intro h; have := hmar W1 0 (Or.inr rfl) (Or.inl rfl)
    rw [add_zero, h, norm_zero] at this; linarith
  obtain ⟨hl1, hl2⟩ := k_facts hl
  set ε : ℝ := min (1 / 8) (c / 8) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 8 := min_le_left _ _
  have hεc : ε ≤ c / 8 := min_le_right _ _
  have hadm0 : RespAdm true l v k1 W1 := ⟨hl, fun _ => ⟨hk1, hv0, hvW⟩⟩
  have hadm1 : RespAdm false k2 W2 k1 W1 := ⟨hk2, fun h => absurd h (by simp)⟩
  obtain ⟨T, ⟨h0c, -⟩, ⟨h1c, -⟩, hC, hR1, hR2, hT0, hT1, hT2⟩ :=
    ((qK_root_facts hadm0 hε).and ((qK_root_facts hadm1 hε).and
      ((respC_eventually_ne hk1 W1).and ((hRoot_facts hk1 W1 hε).and
        ((hRoot_facts hk2 W2 hε).and ((eventually_gt_atTop 0).and
          ((eventually_ge_atTop (8 * ‖v‖)).and (eventually_ge_atTop (16 / c))))))))).exists
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  set q := djq l k1 k2 v W1 W2 with hqdef
  have hq0 : q 0 = qK true (l : ℂ) v (conj v) (k1 : ℂ) W1 (conj W1) := by
    rw [hqdef, djq_zero]; rfl
  have hq1 : q 1 = qK false (k2 : ℂ) W2 (conj W2) (k1 : ℂ) W1 (conj W1) := by
    rw [hqdef, djq_one]; rfl
  have h0 : ((elimPK q 2).eval (C ((respA ((0 : ℝ) : ℂ) 0).eval (T : ℂ)))).eval (T : ℂ) = 0 := by
    rw [← eval_eval_eq_eval_map]
    have : (elimQK ((0 : ℝ) : ℂ) 0 q 2).eval (T : ℂ) = 0 := by rw [hQ, eval_zero]
    exact this
  obtain ⟨p, hp, hs⟩ := exists_roots_of_elimPK_eval q (fun i => by
      rw [hqdef, djq]; exact natDegree_qK_le _ _ _ _ _ _ _) _ 2
    (fun i hi => by
      interval_cases i
      · rw [hq0]; exact h0c
      · rw [hq1]; exact h1c) _ h0
  have hs' : p 0 + p 1 = 0 := by simpa [respA, Finset.sum_range_succ] using hs
  have hp0 := hp 0 (by norm_num)
  have hp1 := hp 1 (by norm_num)
  rw [hq0] at hp0
  rw [hq1] at hp1
  simp only [qK, if_true] at hp0
  simp only [qK, Bool.false_eq_true, if_false, Polynomial.map_pow, eval_pow,
    respQ_eval_hQuad] at hp1
  have hp1' := pow_eq_zero_iff two_ne_zero |>.1 hp1
  obtain ⟨v1, hv1, hj⟩ := exists_of_jQuartic_eval hC hp0
  obtain ⟨hv10, -, hv1re, hv1inv⟩ := hR1 v1 hv1
  obtain ⟨hs0, -, hsre, hsinv⟩ := hR2 (p 1) hp1'
  set s := p 1 with hsdef
  have hp0s : p 0 = -s := by linear_combination hs'
  rw [hp0s, jQuad_neg_eq hTc hv10 hs0] at hj
  have hunit : ((l : ℂ) * T + v + v1 + s) * ((l : ℂ) / T + conj v + v1⁻¹ + s⁻¹) = 1 := by
    have := (mul_eq_zero.1 hj).resolve_left (mul_ne_zero (mul_ne_zero hTc hv10) hs0)
    linear_combination this
  -- the leading part is large
  have hre := re_lead2 hl1 hT0 hT1 hε1 hv1re hsre
  have ha := norm_ge_of_re_div hT0 hre
  -- the constant part is bounded below
  obtain ⟨e1, he1, hd1⟩ := inv_near_choice hv1inv
  obtain ⟨e2, he2, hd2⟩ := inv_near_choice hsinv
  have hm := hmar e1 e2 he1 he2
  have hlT : ‖(l : ℂ) / T‖ ≤ c / 8 := by
    rw [norm_real_div_le (by linarith) hT0, div_le_iff₀ hT0]
    rw [div_le_iff₀ hc] at hT2; nlinarith
  have hb : c / 2 ≤ ‖(l : ℂ) / T + conj v + v1⁻¹ + s⁻¹‖ := by
    have e : (l : ℂ) / T + conj v + v1⁻¹ + s⁻¹ =
        conj (v + e1 + e2) + ((l : ℂ) / T + (v1⁻¹ - conj e1) + (s⁻¹ - conj e2)) := by
      simp only [map_add]; ring
    rw [e]
    have h1 := norm_sub_norm_le (conj (v + e1 + e2))
      (-((l : ℂ) / T + (v1⁻¹ - conj e1) + (s⁻¹ - conj e2)))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_conj] at h1
    have h2 : ‖(l : ℂ) / T + (v1⁻¹ - conj e1) + (s⁻¹ - conj e2)‖ ≤ c / 8 + ε + ε :=
      (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hlT hd1)) hd2)
    linarith
  have hprod := congrArg norm hunit
  rw [norm_mul, norm_one] at hprod
  have hcT : 16 ≤ c * T := by rw [div_le_iff₀ hc] at hT2; linarith
  have : T / 2 * (c / 2) ≤ 1 := by
    rw [← hprod]; exact mul_le_mul ha hb (by positivity) (norm_nonneg _)
  nlinarith

/-! ## §13.3 -/

/-- The response polynomials of §13.3: two two-stage `J` responses. -/
def jjq (l1 l2 k1 k2 : ℝ) (Z1 Z2 W1 W2 : ℂ) : ℕ → ℂ[X][X] :=
  kq (fun _ => true) (djK l1 l2) (djZ Z1 Z2) (djK k1 k2) (djZ W1 W2)

lemma jjq_zero (l1 l2 k1 k2 : ℝ) (Z1 Z2 W1 W2 : ℂ) :
    jjq l1 l2 k1 k2 Z1 Z2 W1 W2 0 = qK true (l1 : ℂ) Z1 (conj Z1) (k1 : ℂ) W1 (conj W1) := by
  simp [jjq, kq, djK, djZ]

lemma jjq_one (l1 l2 k1 k2 : ℝ) (Z1 Z2 W1 W2 : ℂ) :
    jjq l1 l2 k1 k2 Z1 Z2 W1 W2 1 = qK true (l2 : ℂ) Z2 (conj Z2) (k2 : ℂ) W2 (conj W2) := by
  simp [jjq, kq, djK, djZ]

/-- The constant part of a `J` response is close to `conj (Z + e)`, `e ∈ {0, W}`. -/
lemma const_near {l T : ℝ} (hl : l ≤ 2) (hl0 : 0 ≤ l) (hT : 0 < T) {c ε : ℝ} (hTc : 16 / c ≤ T)
    (hc : 0 < c) (hε : ε ≤ c / 8) {Z e v : ℂ} (hd : ‖v⁻¹ - conj e‖ ≤ ε) :
    ‖((l : ℂ) / T + conj Z + v⁻¹) - conj (Z + e)‖ ≤ c / 4 := by
  have hlT : ‖(l : ℂ) / T‖ ≤ c / 8 := by
    rw [norm_real_div_le hl0 hT, div_le_iff₀ hT]
    rw [div_le_iff₀ hc] at hTc; nlinarith
  have e' : ((l : ℂ) / T + conj Z + v⁻¹) - conj (Z + e) = (l : ℂ) / T + (v⁻¹ - conj e) := by
    rw [map_add]; ring
  rw [e']
  linarith [norm_add_le ((l : ℂ) / T) (v⁻¹ - conj e)]

/-- **The eliminated polynomial of §13.3 is not zero**, under the margins `‖Zᵢ + eᵢ‖ ≥ c` and
`‖Z₁ + e₁ + (Z₂ + e₂)‖ ≥ c` for `eᵢ ∈ {0, Wᵢ}`. -/
theorem jj_elim_ne_zero {l1 l2 k1 k2 : ℝ} (hl1 : l1 = 1 ∨ l1 = 2) (hl2 : l2 = 1 ∨ l2 = 2)
    (hk1 : k1 = 1 ∨ k1 = 2) (hk2 : k2 = 1 ∨ k2 = 2) {Z1 Z2 W1 W2 : ℂ} {c : ℝ} (hc : 0 < c)
    (hmar1 : ∀ e1 : ℂ, (e1 = 0 ∨ e1 = W1) → c ≤ ‖Z1 + e1‖)
    (hmar2 : ∀ e2 : ℂ, (e2 = 0 ∨ e2 = W2) → c ≤ ‖Z2 + e2‖)
    (hmar12 : ∀ e1 e2 : ℂ, (e1 = 0 ∨ e1 = W1) → (e2 = 0 ∨ e2 = W2) →
      c ≤ ‖Z1 + e1 + (Z2 + e2)‖) :
    elimQK ((0 : ℝ) : ℂ) 0 (jjq l1 l2 k1 k2 Z1 Z2 W1 W2) 2 ≠ 0 := by
  intro hQ
  have hne : ∀ x : ℂ, c ≤ ‖x‖ → x ≠ 0 := fun x hx h => by rw [h, norm_zero] at hx; linarith
  have hadm1 : RespAdm true l1 Z1 k1 W1 :=
    ⟨hl1, fun _ => ⟨hk1, by simpa using hne _ (hmar1 0 (Or.inl rfl)),
      hne _ (hmar1 W1 (Or.inr rfl))⟩⟩
  have hadm2 : RespAdm true l2 Z2 k2 W2 :=
    ⟨hl2, fun _ => ⟨hk2, by simpa using hne _ (hmar2 0 (Or.inl rfl)),
      hne _ (hmar2 W2 (Or.inr rfl))⟩⟩
  obtain ⟨hl11, hl12⟩ := k_facts hl1
  obtain ⟨hl21, hl22⟩ := k_facts hl2
  set ε : ℝ := min (1 / 8) (c / 8) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 8 := min_le_left _ _
  have hεc : ε ≤ c / 8 := min_le_right _ _
  set B : ℝ := ‖Z1‖ + ‖Z2‖ + ‖W1‖ + ‖W2‖ + c with hBdef
  have hB0 : 0 < B := by positivity
  obtain ⟨T, ⟨h0c, -⟩, ⟨h1c, -⟩, hC1, hC2, hR1, hR2, hT0, hT1, hT2, hT3, hT4⟩ :=
    ((qK_root_facts hadm1 hε).and ((qK_root_facts hadm2 hε).and
      ((respC_eventually_ne hk1 W1).and ((respC_eventually_ne hk2 W2).and
        ((hRoot_facts hk1 W1 hε).and ((hRoot_facts hk2 W2 hε).and
          ((eventually_gt_atTop 0).and ((eventually_ge_atTop (8 * ‖Z1‖)).and
            ((eventually_ge_atTop (8 * ‖Z2‖)).and ((eventually_ge_atTop (16 / c)).and
              (eventually_ge_atTop (5000 * B ^ 2 / c ^ 3)))))))))))).exists
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  set q := jjq l1 l2 k1 k2 Z1 Z2 W1 W2 with hqdef
  have h0 : ((elimPK q 2).eval (C ((respA ((0 : ℝ) : ℂ) 0).eval (T : ℂ)))).eval (T : ℂ) = 0 := by
    rw [← eval_eval_eq_eval_map]
    have : (elimQK ((0 : ℝ) : ℂ) 0 q 2).eval (T : ℂ) = 0 := by rw [hQ, eval_zero]
    exact this
  obtain ⟨p, hp, hs⟩ := exists_roots_of_elimPK_eval q (fun i => by
      rw [hqdef, jjq]; exact natDegree_qK_le _ _ _ _ _ _ _) _ 2
    (fun i hi => by
      interval_cases i
      · rw [hqdef, jjq_zero]; exact h0c
      · rw [hqdef, jjq_one]; exact h1c) _ h0
  have hs' : p 0 + p 1 = 0 := by simpa [respA, Finset.sum_range_succ] using hs
  have hp0 := hp 0 (by norm_num)
  have hp1 := hp 1 (by norm_num)
  rw [hqdef, jjq_zero] at hp0
  rw [hqdef, jjq_one] at hp1
  simp only [qK, if_true] at hp0 hp1
  obtain ⟨v1, hv1, hj1⟩ := exists_of_jQuartic_eval hC1 hp0
  obtain ⟨v2, hv2, hj2⟩ := exists_of_jQuartic_eval hC2 hp1
  obtain ⟨hv10, hv1b, hv1re, hv1inv⟩ := hR1 v1 hv1
  obtain ⟨hv20, hv2b, hv2re, hv2inv⟩ := hR2 v2 hv2
  set t := p 1 with htdef
  have hp0t : p 0 = -t := by linear_combination hs'
  set a1 : ℂ := (l1 : ℂ) * T + Z1 + v1 with ha1
  set a2 : ℂ := (l2 : ℂ) * T + Z2 + v2 with ha2
  set aS1 : ℂ := (l1 : ℂ) / T + conj Z1 + v1⁻¹ with haS1
  set aS2 : ℂ := (l2 : ℂ) / T + conj Z2 + v2⁻¹ with haS2
  rw [hp0t, jQuad_eq_mul hTc hv10] at hj1
  rw [jQuad_eq_mul hTc hv20] at hj2
  have hf : aS1 * t ^ 2 + (a1 * aS1) * t + a1 = 0 := by
    have := (mul_eq_zero.1 hj1).resolve_left (mul_ne_zero hTc hv10)
    linear_combination this
  have hg : aS2 * t ^ 2 + (-(a2 * aS2)) * t + a2 = 0 :=
    (mul_eq_zero.1 hj2).resolve_left (mul_ne_zero hTc hv20)
  have hres := res22_eq_zero_of_common_root hf hg
  rw [res22_hh] at hres
  -- normalised leading coefficients
  set α1 : ℂ := a1 / T with hα1
  set α2 : ℂ := a2 / T with hα2
  have hre1 : 1 / 2 ≤ α1.re := by
    have := re_lead2 hl11 hT0 hT1 hε1 hv1re (y2 := 0) (by simp; linarith)
    rw [add_zero] at this; exact this
  have hre2 : 1 / 2 ≤ α2.re := by
    have := re_lead2 hl21 hT0 hT2 hε1 hv2re (y2 := 0) (by simp; linarith)
    rw [add_zero] at this; exact this
  have hαb : ∀ (l : ℝ) (Z v : ℂ), l ≤ 2 → 0 ≤ l → 8 * ‖Z‖ ≤ T → ‖v / T‖ ≤ 3 →
      ‖((l : ℂ) * T + Z + v) / T‖ ≤ 6 := by
    intro l Z v hl hl0 hZ hv
    have e : ((l : ℂ) * T + Z + v) / T = l + Z / T + v / T := by field_simp
    rw [e]
    have h1 : ‖Z / (T : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le, div_le_iff₀ hT0]; linarith
    have h2 : ‖(l : ℂ)‖ ≤ 2 := by rw [Complex.norm_real, Real.norm_of_nonneg hl0]; exact hl
    linarith [norm_add_le ((l : ℂ) + Z / T) (v / T), norm_add_le (l : ℂ) (Z / T)]
  have hα1b : ‖α1‖ ≤ 6 := hαb l1 Z1 v1 hl12 (by linarith) hT1 hv1b
  have hα2b : ‖α2‖ ≤ 6 := hαb l2 Z2 v2 hl22 (by linarith) hT2 hv2b
  have hα1l : 1 / 2 ≤ ‖α1‖ := hre1.trans (Complex.re_le_norm _)
  have hα2l : 1 / 2 ≤ ‖α2‖ := hre2.trans (Complex.re_le_norm _)
  have hα12 : 1 ≤ ‖α1 + α2‖ := by
    have := Complex.re_le_norm (α1 + α2)
    rw [Complex.add_re] at this; linarith
  -- constant coefficients
  obtain ⟨e1, he1, hd1⟩ := inv_near_choice hv1inv
  obtain ⟨e2, he2, hd2⟩ := inv_near_choice hv2inv
  have hn1 := const_near (Z := Z1) hl12 (by linarith) hT0 hT3 hc hεc hd1
  have hn2 := const_near (Z := Z2) hl22 (by linarith) hT0 hT3 hc hεc hd2
  rw [← haS1] at hn1
  rw [← haS2] at hn2
  have hm1 := hmar1 e1 he1
  have hm2 := hmar2 e2 he2
  have hm12 := hmar12 e1 e2 he1 he2
  have hS1l : c / 2 ≤ ‖aS1‖ := by
    have := norm_sub_norm_le (conj (Z1 + e1)) (conj (Z1 + e1) - aS1)
    rw [sub_sub_cancel, Complex.norm_conj, norm_sub_rev] at this; linarith
  have hS2l : c / 2 ≤ ‖aS2‖ := by
    have := norm_sub_norm_le (conj (Z2 + e2)) (conj (Z2 + e2) - aS2)
    rw [sub_sub_cancel, Complex.norm_conj, norm_sub_rev] at this; linarith
  have hS12l : c / 2 ≤ ‖aS1 + aS2‖ := by
    have e' : aS1 + aS2 = conj (Z1 + e1 + (Z2 + e2)) + ((aS1 - conj (Z1 + e1)) +
        (aS2 - conj (Z2 + e2))) := by rw [map_add (starRingEnd ℂ) (Z1 + e1)]; ring
    rw [e']
    have := norm_sub_norm_le (conj (Z1 + e1 + (Z2 + e2)))
      (-((aS1 - conj (Z1 + e1)) + (aS2 - conj (Z2 + e2))))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_conj] at this
    linarith [norm_add_le (aS1 - conj (Z1 + e1)) (aS2 - conj (Z2 + e2))]
  have hEb : ∀ (Z e W : ℂ), (e = 0 ∨ e = W) → ‖Z + e‖ ≤ ‖Z‖ + ‖W‖ := by
    intro Z e W he
    rcases he with rfl | rfl
    · simp
    · exact norm_add_le _ _
  have hS1u : ‖aS1‖ ≤ B := by
    have := norm_le_norm_add_norm_sub' aS1 (conj (Z1 + e1))
    rw [Complex.norm_conj] at this
    have := hEb Z1 e1 W1 he1
    rw [hBdef]; linarith [norm_nonneg Z2, norm_nonneg W2]
  have hS2u : ‖aS2‖ ≤ B := by
    have := norm_le_norm_add_norm_sub' aS2 (conj (Z2 + e2))
    rw [Complex.norm_conj] at this
    have := hEb Z2 e2 W2 he2
    rw [hBdef]; linarith [norm_nonneg Z1, norm_nonneg W1]
  -- the (H1) expression in normalised form
  set P : ℂ := α1 * α2 * (α1 + α2) * (aS1 * aS2 * (aS1 + aS2)) with hP
  set Q : ℂ := (α1 * aS2 - aS1 * α2) ^ 2 with hQdef
  have ha1e : a1 = T * α1 := by rw [hα1]; field_simp
  have ha2e : a2 = T * α2 := by rw [hα2]; field_simp
  have hexp : QuadraticResponse.hhExpr a1 aS1 a2 aS2 = (T : ℂ) ^ 2 * ((T : ℂ) * P + Q) := by
    rw [ha1e, ha2e, QuadraticResponse.hhExpr, hP, hQdef]; ring
  rw [hexp] at hres
  have hTPQ : (T : ℂ) * P + Q = 0 :=
    (mul_eq_zero.1 hres).resolve_left (pow_ne_zero 2 hTc)
  have hPl : c ^ 3 / 32 ≤ ‖P‖ := by
    rw [hP, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    have h1 : 1 / 2 * (1 / 2) * 1 ≤ ‖α1‖ * ‖α2‖ * ‖α1 + α2‖ :=
      mul_le_mul (mul_le_mul hα1l hα2l (by norm_num) (by linarith)) hα12 (by norm_num)
        (by positivity)
    have h2 : c / 2 * (c / 2) * (c / 2) ≤ ‖aS1‖ * ‖aS2‖ * ‖aS1 + aS2‖ :=
      mul_le_mul (mul_le_mul hS1l hS2l (by positivity) (by linarith)) hS12l (by positivity)
        (by positivity)
    have := mul_le_mul h1 h2 (by positivity) (by positivity)
    calc c ^ 3 / 32 = 1 / 2 * (1 / 2) * 1 * (c / 2 * (c / 2) * (c / 2)) := by ring
      _ ≤ _ := this
  have hQu : ‖Q‖ ≤ 144 * B ^ 2 := by
    rw [hQdef, norm_pow]
    have h1 : ‖α1 * aS2 - aS1 * α2‖ ≤ 12 * B := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have := mul_le_mul hα1b hS2u (norm_nonneg _) (by norm_num)
      have := mul_le_mul hS1u hα2b (norm_nonneg _) hB0.le
      linarith
    calc ‖α1 * aS2 - aS1 * α2‖ ^ 2 ≤ (12 * B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = 144 * B ^ 2 := by ring
  have hTP : ‖(T : ℂ) * P‖ = ‖Q‖ := by
    rw [show (T : ℂ) * P = -Q by linear_combination hTPQ, norm_neg]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT0.le] at hTP
  have hT4' : 5000 * B ^ 2 ≤ T * c ^ 3 := by rwa [div_le_iff₀ (by positivity)] at hT4
  have : T * (c ^ 3 / 32) ≤ 144 * B ^ 2 := by
    rw [← hTP] at hQu
    exact (mul_le_mul_of_nonneg_left hPl hT0.le).trans hQu
  have h5 : T * c ^ 3 ≤ 4608 * B ^ 2 := by linarith
  have hB2 : 0 < B ^ 2 := by positivity
  linarith

end CaplessKElim

end Erdos99
end

end FlaggedPoly

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FlaggedPinning`
-/

section FlaggedPinning

/-!
# Approximate relations of §§13.2–13.3 pin the direction (Verification Guide §12.4–§12.5)

* `pinning_of_exact`, `directions_few_of_exact`: the compactness argument of
  `capless_pinningK` / `capless_directions_fewK` for an arbitrary compact set `Adm` of data and a
  fixed port type `b`, given a uniform bound `N` on the exact solutions;
* `defJAdm R c`, `jjAdm R c`: the admissible data of §13.2 and §13.3 (`k₀ = 0`, `Z₀ = 0`, bounded
  data, multiplicities in `{1, 2}`, and the margins of the constant coefficients);
* `defJ_exact_card_le`, `jj_exact_card_le`: their exact solutions lie in at most `capDegK 2`
  directions (from `defJ_elim_ne_zero`, `jj_elim_ne_zero`).
-/

open Filter Topology Metric ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace CaplessKElim

open CaplessElim

/-- The compact set of states over a set of data. -/
def statesOf {m : ℕ} (Adm : Set (CapDataK m)) : Set (CapStateK m) :=
  Adm ×ˢ sphere 0 1 ×ˢ Set.univ.pi (fun _ => sphere (0 : ℂ) 1) ×ˢ
    Set.univ.pi (fun _ => sphere (0 : ℂ) 1) ×ˢ Set.univ.pi (fun _ => sphere (0 : ℂ) 1) ×ˢ
    Set.univ.pi (fun _ => sphere (0 : ℂ) 1)

lemma isCompact_statesOf {m : ℕ} {Adm : Set (CapDataK m)} (hA : IsCompact Adm) :
    IsCompact (statesOf Adm) :=
  hA.prod ((isCompact_sphere _ _).prod
    ((isCompact_univ_pi fun _ => isCompact_sphere _ _).prod
      ((isCompact_univ_pi fun _ => isCompact_sphere _ _).prod
        ((isCompact_univ_pi fun _ => isCompact_sphere _ _).prod
          (isCompact_univ_pi fun _ => isCompact_sphere _ _)))))

set_option synthInstance.maxSize 512 in
/-- **Approximate relations pin the direction** (compactness), for a compact set of data whose
exact solutions lie in at most `N` directions. -/
theorem pinning_of_exact (m : ℕ) (b : Fin m → Bool) {Adm : Set (CapDataK m)}
    (hAc : IsCompact Adm) (N : ℕ)
    (hex : ∀ d ∈ Adm, ∃ S : Finset ℂ, S.card ≤ N ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : Fin m → ℂ,
      (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1) → capRes0K d ζ p = 0 →
      (∀ i, capRes1K b d ζ p u v w i = 0) → ζ ∈ S)
    {w : ℝ} (hw : 0 < w) :
    ∃ r > 0, ∃ μ > 0, ∀ (c' : CapDataK m) (A : Finset ℂ),
      (∀ ζ ∈ A, ‖ζ‖ = 1 ∧ ∃ d ∈ Adm, ‖d - c'‖ < μ ∧ CapApproxK m r b d ζ) →
      (A : Set ℂ).Pairwise (fun a b => w ≤ ‖a - b‖) → A.card ≤ N := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ s : Fin (N + 1) → CapStateK m, (∀ j, s j ∈ statesOf Adm) ∧
      (∀ j j', ‖(s j).1 - (s j').1‖ < 2 / (n + 1)) ∧
      (∀ j j', j ≠ j' → w ≤ ‖(s j).2.1 - (s j').2.1‖) ∧
      (∀ j, capRes0K (s j).1 (s j).2.1 (s j).2.2.1 < 1 / (n + 1)) ∧
      (∀ j i, capRes1K b (s j).1 (s j).2.1 (s j).2.2.1 (s j).2.2.2.1 (s j).2.2.2.2.1
        (s j).2.2.2.2.2 i < 1 / (n + 1)) := by
    intro n
    obtain ⟨c', A, hA, hsep, hcard⟩ := hcon (1 / (n + 1)) (by positivity) (1 / (n + 1))
      (by positivity)
    obtain ⟨A', hA'A, hA'card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcard)
    set e := A'.equivFin
    have hmem : ∀ j : Fin (N + 1), ((e.symm (Fin.cast hA'card.symm j)) : ℂ) ∈ A :=
      fun j => hA'A (e.symm _).2
    choose hζ1 d hdK hdc p u v w' hpu h0 h1 using fun j => hA _ (hmem j)
    refine ⟨fun j => (d j, (e.symm (Fin.cast hA'card.symm j) : ℂ), p j, u j, v j, w' j),
      fun j => ?_, fun j j' => ?_, fun j j' hjj' => ?_, fun j => h0 j, fun j i => h1 j i⟩
    · refine ⟨hdK j, ?_, fun i _ => ?_, fun i _ => ?_, fun i _ => ?_, fun i _ => ?_⟩
      · simpa using hζ1 j
      · simpa using (hpu j i).1
      · simpa using (hpu j i).2.1
      · simpa using (hpu j i).2.2.1
      · simpa using (hpu j i).2.2.2
    · calc ‖d j - d j'‖ = ‖(d j - c') - (d j' - c')‖ := by congr 1; abel
        _ ≤ ‖d j - c'‖ + ‖d j' - c'‖ := norm_sub_le _ _
        _ < 1 / (n + 1) + 1 / (n + 1) := add_lt_add (hdc j) (hdc j')
        _ = 2 / (n + 1) := by ring
    · refine hsep (Finset.mem_coe.2 (hmem j)) (Finset.mem_coe.2 (hmem j')) ?_
      intro heq
      apply hjj'
      have := Subtype.ext heq
      have := e.symm.injective this
      exact Fin.cast_injective _ this
  choose s hsK hsd hsw hs0 hs1 using hseq
  have hK : IsCompact (Set.univ.pi fun _ : Fin (N + 1) => statesOf Adm) :=
    isCompact_univ_pi fun _ => isCompact_statesOf hAc
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
      simpa [mul_one_div] using hinv.const_mul 2
    exact sub_eq_zero.1 (tendsto_nhds_unique ht ht0)
  have hres0 : ∀ j, capRes0K (a j).1 (a j).2.1 (a j).2.2.1 = 0 := by
    intro j
    have ht := ((continuous_capRes0K m).tendsto _).comp (hlimj j)
    refine le_antisymm (le_of_tendsto_of_tendsto' ht hinv fun n => (hs0 (φ n) j).le) ?_
    exact norm_nonneg _
  have hres1 : ∀ j i, capRes1K b (a j).1 (a j).2.1 (a j).2.2.1 (a j).2.2.2.1 (a j).2.2.2.2.1
      (a j).2.2.2.2.2 i = 0 := by
    intro j i
    have ht := ((continuous_capRes1K m b i).tendsto _).comp (hlimj j)
    refine le_antisymm (le_of_tendsto_of_tendsto' ht hinv fun n => (hs1 (φ n) j i).le) ?_
    unfold capRes1K
    split_ifs <;> positivity
  have hsep : ∀ j j', j ≠ j' → w ≤ ‖(a j).2.1 - (a j').2.1‖ := by
    intro j j' hjj'
    have ht : Tendsto (fun n => ‖(s (φ n) j).2.1 - (s (φ n) j').2.1‖) atTop
        (𝓝 ‖(a j).2.1 - (a j').2.1‖) :=
      (((continuous_fst.comp continuous_snd).tendsto _).comp (hlimj j)).sub
        (((continuous_fst.comp continuous_snd).tendsto _).comp (hlimj j')) |>.norm
    exact ge_of_tendsto' ht fun n => hsw (φ n) j j' hjj'
  obtain ⟨S, hS, hsol⟩ := hex _ (ha 0 (Set.mem_univ _)).1
  have hmemS : ∀ j, (a j).2.1 ∈ S := by
    intro j
    have hj := ha j (Set.mem_univ _)
    obtain ⟨-, hζ, hp, hu, hv, hw'⟩ := hj
    refine hsol _ (by simpa using hζ) (a j).2.2.1 (a j).2.2.2.1 (a j).2.2.2.2.1 (a j).2.2.2.2.2
      (fun i => ⟨by simpa using hp i (Set.mem_univ _), by simpa using hu i (Set.mem_univ _),
        by simpa using hv i (Set.mem_univ _), by simpa using hw' i (Set.mem_univ _)⟩) ?_ ?_
    · rw [← hdata j]; exact hres0 j
    · intro i; rw [← hdata j]; exact hres1 j i
  have hinj : Function.Injective (fun j => (a j).2.1) := by
    intro j j' h
    by_contra hne
    have := hsep j j' hne
    simp only at h
    rw [h, sub_self, norm_zero] at this
    linarith
  have := Finset.card_le_card_of_injOn (s := Finset.univ) (fun j => (a j).2.1)
    (fun j _ => hmemS j) hinj.injOn
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **Hull directions pinned by approximate relations are few.** -/
theorem directions_few_of_exact (m : ℕ) (b : Fin m → Bool) {Adm : Set (CapDataK m)}
    (hAc : IsCompact Adm) (N : ℕ)
    (hex : ∀ d ∈ Adm, ∃ S : Finset ℂ, S.card ≤ N ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : Fin m → ℂ,
      (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1) → capRes0K d ζ p = 0 →
      (∀ i, capRes1K b d ζ p u v w i = 0) → ζ ∈ S)
    (Nc : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ Cs : Finset (CapDataK m), Cs.card ≤ Nc →
      ∀ A ⊆ ccwHullSides X, (∀ p ∈ A, ∃ d ∈ Adm,
        (∃ c' ∈ Cs, ‖d - c'‖ < μ) ∧ CapApproxK m r b d (toC (sideDir p))) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨C, hC, hcount⟩ := card_sides_near_finset
  set K : ℝ := Nc * N with hK
  have hK0 : 0 ≤ K := by positivity
  set w : ℝ := min 1 (ε / (2 * (C * K + 1))) with hw
  have hw0 : 0 < w := lt_min one_pos (by positivity)
  have hw1 : w ≤ 1 := min_le_left _ _
  obtain ⟨r, hr, μ, hμ, hpin⟩ := pinning_of_exact m b hAc N hex hw0
  refine ⟨r, hr, μ, hμ, ?_⟩
  have hsmall : ∀ᶠ n in atTop, minDiam n ^ (-(1 / 9 : ℝ)) ≤ w :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp tendsto_minDiam).eventually
      (Iic_mem_nhds hw0)
  filter_upwards [hcount, hsmall] with n hn hsm X hX Cs hCs A hA hpA
  rw [← hX.diam_eq] at hsm
  set T : CapDataK m → Finset ℂ := fun c' =>
    (A.filter (fun p => ∃ d ∈ Adm, ‖d - c'‖ < μ ∧
      CapApproxK m r b d (toC (sideDir p)))).image (fun p => toC (sideDir p))
  have hunit : ∀ p ∈ A, ‖toC (sideDir p)‖ = 1 := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 (hA hp)).2.2.2.1
    rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
  choose! Sc hScT hScsep hScdense using fun c' => CaplessElim.exists_maximal_separated (T c') hw0
  have hSccard : ∀ c', (Sc c').card ≤ N := by
    intro c'
    refine hpin c' (Sc c') (fun ζ hζ => ?_) (hScsep c')
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (hScT c' hζ)
    obtain ⟨hpA', d, hd, hdc, hap⟩ := Finset.mem_filter.1 hp
    exact ⟨hunit p hpA', d, hd, hdc, hap⟩
  set S : Finset ℂ := Cs.biUnion Sc with hS
  have hScard : (S.card : ℝ) ≤ K := by
    have h1 : S.card ≤ Nc * N := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ c' ∈ Cs, (Sc c').card ≤ ∑ _c' ∈ Cs, N := Finset.sum_le_sum fun c' _ => hSccard c'
        _ = Cs.card * N := by simp
        _ ≤ Nc * N := Nat.mul_le_mul_right _ hCs
    rw [hK]
    exact_mod_cast h1
  have hsub : A ⊆ (ccwHullSides X).filter (fun p => ∃ s ∈ S, ‖toC (sideDir p) - s‖ ≤ w) := by
    intro p hp
    refine Finset.mem_filter.2 ⟨hA hp, ?_⟩
    obtain ⟨d, hd, ⟨c', hc', hdc⟩, hap⟩ := hpA p hp
    have hT : toC (sideDir p) ∈ T c' :=
      Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp, d, hd, hdc, hap⟩, rfl⟩
    obtain ⟨s, hs, hps⟩ := hScdense c' _ hT
    exact ⟨s, Finset.mem_biUnion.2 ⟨c', hc', hs⟩, hps.le⟩
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

/-! ## The admissible data of §§13.2–13.3 -/

/-- The bounded data with `k₀ = 0` and `Z₀ = 0`. -/
def zeroBox (R : ℝ) : Set (CapDataK 2) :=
  ({0} : Set ℝ) ×ˢ ({0} : Set ℂ) ×ˢ Set.univ.pi (fun _ => ({1, 2} : Set ℝ)) ×ˢ
    Set.univ.pi (fun _ => closedBall (0 : ℂ) R) ×ˢ Set.univ.pi (fun _ => ({1, 2} : Set ℝ)) ×ˢ
    Set.univ.pi (fun _ => closedBall (0 : ℂ) R)

lemma isCompact_zeroBox (R : ℝ) : IsCompact (zeroBox R) :=
  isCompact_singleton.prod (isCompact_singleton.prod
    ((isCompact_univ_pi fun _ => (Set.toFinite _).isCompact).prod
      ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod
        ((isCompact_univ_pi fun _ => (Set.toFinite _).isCompact).prod
          (isCompact_univ_pi fun _ => isCompact_closedBall _ _)))))

/-- The port types of §13.2: the first port is a two-stage `J` response, the second an `H`
response. -/
def defJB : Fin 2 → Bool := fun i => decide (i.val = 0)

/-- The margins of §13.2: with `v = Z 0` (the retained vector of the `J` face), `W₁ = W 0` and
`W₂ = Z 1` (the retained sums of its two `H` neighbours), `‖v + e₁ + e₂‖ ≥ c` for
`eᵢ ∈ {0, Wᵢ}`. -/
def defJMargin (c : ℝ) : Set (CapDataK 2) :=
  {d | c ≤ ‖d.2.2.2.1 0‖ ∧ c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0‖ ∧
    c ≤ ‖d.2.2.2.1 0 + d.2.2.2.1 1‖ ∧ c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0 + d.2.2.2.1 1‖}

/-- The admissible data of §13.2. -/
def defJAdm (R c : ℝ) : Set (CapDataK 2) := zeroBox R ∩ defJMargin c

/-- The margins of §13.3: `‖Zᵢ + eᵢ‖ ≥ c` and `‖Z₀ + e₀ + (Z₁ + e₁)‖ ≥ c` for `eᵢ ∈ {0, Wᵢ}`. -/
def jjMargin (c : ℝ) : Set (CapDataK 2) :=
  {d | c ≤ ‖d.2.2.2.1 0‖ ∧ c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0‖ ∧ c ≤ ‖d.2.2.2.1 1‖ ∧
    c ≤ ‖d.2.2.2.1 1 + d.2.2.2.2.2 1‖ ∧ c ≤ ‖d.2.2.2.1 0 + d.2.2.2.1 1‖ ∧
    c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0 + d.2.2.2.1 1‖ ∧
    c ≤ ‖d.2.2.2.1 0 + (d.2.2.2.1 1 + d.2.2.2.2.2 1)‖ ∧
    c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0 + (d.2.2.2.1 1 + d.2.2.2.2.2 1)‖}

/-- The admissible data of §13.3. -/
def jjAdm (R c : ℝ) : Set (CapDataK 2) := zeroBox R ∩ jjMargin c

lemma isCompact_defJAdm (R c : ℝ) : IsCompact (defJAdm R c) := by
  refine (isCompact_zeroBox R).inter_right ?_
  have h : ∀ f : CapDataK 2 → ℂ, Continuous f → IsClosed {d : CapDataK 2 | c ≤ ‖f d‖} :=
    fun f hf => isClosed_le continuous_const hf.norm
  have e : defJMargin c = {d : CapDataK 2 | c ≤ ‖d.2.2.2.1 0‖} ∩
      ({d | c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0‖} ∩ ({d | c ≤ ‖d.2.2.2.1 0 + d.2.2.2.1 1‖} ∩
        {d | c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0 + d.2.2.2.1 1‖})) := by
    ext d; simp [defJMargin]
  rw [e]
  exact (h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter
    (h _ (by fun_prop))))

lemma isCompact_jjAdm (R c : ℝ) : IsCompact (jjAdm R c) := by
  refine (isCompact_zeroBox R).inter_right ?_
  have h : ∀ f : CapDataK 2 → ℂ, Continuous f → IsClosed {d : CapDataK 2 | c ≤ ‖f d‖} :=
    fun f hf => isClosed_le continuous_const hf.norm
  have e : jjMargin c = {d : CapDataK 2 | c ≤ ‖d.2.2.2.1 0‖} ∩
      ({d | c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0‖} ∩ ({d | c ≤ ‖d.2.2.2.1 1‖} ∩
        ({d | c ≤ ‖d.2.2.2.1 1 + d.2.2.2.2.2 1‖} ∩ ({d | c ≤ ‖d.2.2.2.1 0 + d.2.2.2.1 1‖} ∩
          ({d | c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0 + d.2.2.2.1 1‖} ∩
            ({d | c ≤ ‖d.2.2.2.1 0 + (d.2.2.2.1 1 + d.2.2.2.2.2 1)‖} ∩
              {d | c ≤ ‖d.2.2.2.1 0 + d.2.2.2.2.2 0 + (d.2.2.2.1 1 + d.2.2.2.2.2 1)‖})))))) := by
    ext d; simp [jjMargin]
  rw [e]
  exact (h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter
    ((h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter
      ((h _ (by fun_prop)).inter (h _ (by fun_prop))))))))

/-- Extending exact solutions on `Fin 2` to `ℕ`. -/
lemma exact_of_ne_fin2 (b : Fin 2 → Bool) (d : CapDataK 2)
    (hne : elimQK (d.1 : ℂ) d.2.1 (kq (extB b)
      (fun i => if h : i < 2 then d.2.2.1 ⟨i, h⟩ else 1)
      (fun i => if h : i < 2 then d.2.2.2.1 ⟨i, h⟩ else 0)
      (fun i => if h : i < 2 then d.2.2.2.2.1 ⟨i, h⟩ else 1)
      (fun i => if h : i < 2 then d.2.2.2.2.2 ⟨i, h⟩ else 0)) 2 ≠ 0) :
    ∃ S : Finset ℂ, S.card ≤ capDegK 2 ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : Fin 2 → ℂ,
      (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1) → capRes0K d ζ p = 0 →
      (∀ i, capRes1K b d ζ p u v w i = 0) → ζ ∈ S := by
  set ext : (Fin 2 → ℂ) → ℕ → ℂ := fun f i => if h : i < 2 then f ⟨i, h⟩ else 0 with hext
  obtain ⟨S, hS, hsol⟩ := solutions_card_le_of_ne _ _ _ _ _ _ _ 2 hne
  refine ⟨S, hS, fun ζ hζ p u v w hpu h0 h1 => ?_⟩
  refine hsol ζ hζ (ext p) (ext u) (ext v) (ext w) (fun i hi => ?_) ?_
  · simp only [extB, ext, dif_pos hi]
    obtain ⟨h1p, h1u, h1v, h1w⟩ := hpu ⟨i, hi⟩
    refine ⟨h1p, h1u, h1v, h1w, ?_⟩
    have h := h1 ⟨i, hi⟩
    unfold capRes1K at h
    split_ifs at h ⊢ with hb
    · have ha := norm_nonneg ((d.2.2.1 ⟨i, hi⟩ : ℂ) * ζ + d.2.2.2.1 ⟨i, hi⟩ - p ⟨i, hi⟩ +
        v ⟨i, hi⟩ + u ⟨i, hi⟩)
      have hb' := norm_nonneg ((d.2.2.2.2.1 ⟨i, hi⟩ : ℂ) * ζ + d.2.2.2.2.2 ⟨i, hi⟩ - v ⟨i, hi⟩ +
        w ⟨i, hi⟩)
      exact ⟨norm_eq_zero.1 (by linarith), norm_eq_zero.1 (by linarith)⟩
    · exact norm_eq_zero.1 h
  · have : ∑ i ∈ Finset.range 2, ext p i = ∑ i, p i := by
      rw [Finset.sum_range (fun i => ext p i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [ext, i.2]
    rw [this]
    exact norm_eq_zero.1 h0

/-- **Exact solutions of §13.2 lie in few directions.** -/
theorem defJ_exact_card_le (R : ℝ) {c : ℝ} (hc : 0 < c) {d : CapDataK 2}
    (hd : d ∈ defJAdm R c) :
    ∃ S : Finset ℂ, S.card ≤ capDegK 2 ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : Fin 2 → ℂ,
      (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1) → capRes0K d ζ p = 0 →
      (∀ i, capRes1K defJB d ζ p u v w i = 0) → ζ ∈ S := by
  obtain ⟨⟨hd0, hz0, hk, -, hk2, -⟩, hm1, hm2, hm3, hm4⟩ := hd
  refine exact_of_ne_fin2 defJB d ?_
  rw [Set.mem_singleton_iff.1 hd0, Set.mem_singleton_iff.1 hz0]
  rw [elimQK_congr (q' := djq (d.2.2.1 0) (d.2.2.2.2.1 0) (d.2.2.1 1) (d.2.2.2.1 0)
    (d.2.2.2.2.2 0) (d.2.2.2.1 1)) (fun i hi => by
      interval_cases i <;> simp [kq, djq, extB, defJB, djB, djK, djZ, qK])]
  refine defJ_elim_ne_zero (hk 0 trivial) (hk2 0 trivial) (hk 1 trivial) hc ?_
  intro e1 e2 he1 he2
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;> simpa using ‹_›

/-- **Exact solutions of §13.3 lie in few directions.** -/
theorem jj_exact_card_le (R : ℝ) {c : ℝ} (hc : 0 < c) {d : CapDataK 2}
    (hd : d ∈ jjAdm R c) :
    ∃ S : Finset ℂ, S.card ≤ capDegK 2 ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u v w : Fin 2 → ℂ,
      (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ ‖v i‖ = 1 ∧ ‖w i‖ = 1) → capRes0K d ζ p = 0 →
      (∀ i, capRes1K (fun _ => true) d ζ p u v w i = 0) → ζ ∈ S := by
  obtain ⟨⟨hd0, hz0, hk, -, hk2, -⟩, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8⟩ := hd
  refine exact_of_ne_fin2 (fun _ => true) d ?_
  rw [Set.mem_singleton_iff.1 hd0, Set.mem_singleton_iff.1 hz0]
  rw [elimQK_congr (q' := jjq (d.2.2.1 0) (d.2.2.1 1) (d.2.2.2.2.1 0) (d.2.2.2.2.1 1)
    (d.2.2.2.1 0) (d.2.2.2.1 1) (d.2.2.2.2.2 0) (d.2.2.2.2.2 1)) (fun i hi => by
      interval_cases i <;> simp [kq, jjq, extB, djK, djZ])]
  refine jj_elim_ne_zero (hk 0 trivial) (hk 1 trivial) (hk2 0 trivial) (hk2 1 trivial) hc
    ?_ ?_ ?_
  · intro e1 he1; rcases he1 with rfl | rfl <;> simpa using ‹_›
  · intro e2 he2; rcases he2 with rfl | rfl <;> simpa using ‹_›
  · intro e1 e2 he1 he2
    rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;> simpa using ‹_›

end CaplessKElim

end Erdos99
end

end FlaggedPinning

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FlaggedGeometry`
-/

section FlaggedGeometry

/-!
# The geometric reduction of §§13.2–13.3

* `J_ports_equation`: the closure equation at a degree-three face, in terms of the port vectors of
  two of its unmarked short ports;
* `re_longSum_le`, `norm_ge_of_re_le`: the margin of the retained sums of unflagged faces relative
  to a common tangent;
* `zeroCentres`: the centres of the data of §§13.2–13.3, built from the cluster centres of the long
  sides;
* `defJ_witness` (§13.2): an unflagged `J` face with two matched ports to unflagged degree-two
  faces, all away from the exceptional faces of the clustering, gives admissible data close to a
  centre with an approximate solution at its label direction;
* `jj_witness` (§13.3): the same for an unflagged `J` face with a matched port to an unflagged
  degree-two face and a matched port to another unflagged `J` face with the same property.
-/

open scoped BigOperators Real
open Filter ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim CaplessKElim

/-! ## Pure lemmas -/

/-- Replacing a label direction by a nearby direction `ζ`. -/
lemma kmul_repl {k : ℝ} (hk : k = 1 ∨ k = 2) {τ ζ x : ℂ} {ρ : ℝ} (h : ‖τ - ζ‖ ≤ ρ) :
    ‖(k : ℂ) * ζ + x‖ ≤ ‖(k : ℂ) * τ + x‖ + 2 * ρ := by
  have e : (k : ℂ) * ζ + x = ((k : ℂ) * τ + x) + (k : ℂ) * (ζ - τ) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_mul, norm_sub_rev]
  have hk2 : ‖(k : ℂ)‖ ≤ 2 := by rcases hk with rfl | rfl <;> norm_num
  exact mul_le_mul hk2 h (norm_nonneg _) (by norm_num)

/-- A unit vector with projection `≤ -θ` on `τ` has projection `≤ -θ + ρ` on `ζ` if
`‖τ - ζ‖ ≤ ρ`. -/
lemma re_shift {z τ ζ : ℂ} (hz : ‖z‖ = 1) {θ ρ : ℝ} (h : (z * conj τ).re ≤ -θ)
    (hτ : ‖τ - ζ‖ ≤ ρ) : (z * conj ζ).re ≤ -θ + ρ := by
  have e : z * conj ζ = z * conj τ + z * conj (ζ - τ) := by rw [map_sub]; ring
  rw [e, Complex.add_re]
  have h2 : (z * conj (ζ - τ)).re ≤ ρ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj, hz, one_mul, norm_sub_rev]; exact hτ
  linarith

lemma re_longSum_le {A : Finset (ℂ × ℂ)} {ζ : ℂ} {c : ℝ}
    (h : ∀ ab ∈ A, ((ab.2 - ab.1) * conj ζ).re ≤ -c) :
    ((∑ ab ∈ A, (ab.2 - ab.1)) * conj ζ).re ≤ -(c * A.card) := by
  rw [Finset.sum_mul, Complex.re_sum]
  calc ∑ ab ∈ A, ((ab.2 - ab.1) * conj ζ).re ≤ ∑ _ab ∈ A, -c := Finset.sum_le_sum h
    _ = -(c * A.card) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma norm_ge_of_re_le {x ζ : ℂ} (hζ : ‖ζ‖ = 1) {c : ℝ} (h : (x * conj ζ).re ≤ -c) :
    c ≤ ‖x‖ := by
  have h1 := Complex.re_le_norm (-(x * conj ζ))
  rw [Complex.neg_re, norm_neg, norm_mul, Complex.norm_conj, hζ, mul_one] at h1
  linarith

lemma inner_eq_re_mul_conj (z w : ℂ) : inner ℝ z w = (z * conj w).re := by
  rw [Complex.inner]; simp [Complex.mul_re]; ring

/-! ## The closure equation with port vectors -/

/-- **The closure equation at a degree-three face, with port vectors.** -/
theorem J_ports_equation :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ q1 ∈ unmarkedPorts X L G mk, ∀ q2 ∈ unmarkedPorts X L G mk, q1.1 = q2.1 →
        (trackGraph X L G mk).deg q1.1 = 3 → q1 ≠ q2 →
        ∃ u : ℂ, ‖u‖ = 1 ∧ ‖(G.kMult q1.1 : ℂ) * labDir lab q1.1 + portVec X q1 + portVec X q2 +
          u + longSum X L q1.1‖ ≤ tol := by
  filter_upwards [J_face_equation, exists_side_of_port] with n hface hside hfm X hX htri L tol G mk
    lab hmk hlab q1 hq1 q2 hq2 h12 hdeg hne
  obtain ⟨hg1, hsp1, hnm1⟩ := mem_unmarkedPorts.1 hq1
  obtain ⟨hg2, hsp2, hnm2⟩ := mem_unmarkedPorts.1 hq2
  rw [← h12] at hsp2 hnm2
  obtain ⟨-, hp1, -⟩ := Finset.mem_filter.1 hsp1
  obtain ⟨-, hp2, -⟩ := Finset.mem_filter.1 hsp2
  obtain ⟨ab1, hab1, habe1⟩ := hside hfm X hX _ _ hp1
  obtain ⟨ab2, hab2, habe2⟩ := hside hfm X hX _ _ hp2
  have hne2 : q1.2 ≠ q2.2 := fun h => hne (Prod.ext h12 h)
  obtain ⟨u, hu, h⟩ := hface hfm X hX htri L tol G mk lab hmk hlab _ hg1 hdeg _
    (Finset.mem_sdiff.2 ⟨hsp1, hnm1⟩) _ (Finset.mem_sdiff.2 ⟨hsp2, hnm2⟩) hne2 ab1 hab1 habe1
    ab2 hab2 habe2
  have hFe : q1.1 ∈ exceptionalFaces X := (mem_exceptionalFinset hX.1.2).1 (G.good_subset hg1)
  have hne' := nonempty_of_mem_exceptionalFaces hFe
  have e1 := portVec_eq hne' hab1 habe1
  have e2 := portVec_eq (q := q2) (by rw [← h12]; exact hne') (by rw [← h12]; exact hab2) habe2
  rw [← e1, ← e2] at h
  exact ⟨u, hu, h⟩

/-- Port vectors of unmarked ports are unit vectors. -/
theorem portVec_unit :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
      ∀ q ∈ unmarkedPorts X L G mk, ‖portVec X q‖ = 1 := by
  filter_upwards [exists_side_of_port, face_side_facts] with n hside hfacts hfm X hX L G mk q hq
  obtain ⟨hFg, hsp, -⟩ := mem_unmarkedPorts.1 hq
  obtain ⟨-, hpF, -⟩ := Finset.mem_filter.1 hsp
  obtain ⟨ab, hab, habe⟩ := hside hfm X hX _ _ hpF
  rw [portVec_eq (nonempty_of_mem_exceptionalFaces hpF.1) hab habe]
  exact (hfacts hfm X hX G _ hFg).2 ab hab

/-! ## Centres -/

/-- The centres of the data of §§13.2–13.3. -/
def zeroCentres (U : Finset ℂ) : Finset (CapDataK 2) :=
  ({0} : Finset ℝ) ×ˢ ({0} : Finset ℂ) ×ˢ
    Fintype.piFinset (fun _ : Fin 2 => ({1, 2} : Finset ℝ)) ×ˢ
    Fintype.piFinset (fun _ : Fin 2 => sumCentresK U 6) ×ˢ
    Fintype.piFinset (fun _ : Fin 2 => ({1, 2} : Finset ℝ)) ×ˢ
    Fintype.piFinset (fun _ : Fin 2 => sumCentresK U 6)

/-- The bound on the number of centres. -/
def zeroNcent (Nc : ℕ) : ℕ := 16 * (7 ^ Nc) ^ 4

lemma card_zeroCentres_le {U : Finset ℂ} {Nc : ℕ} (hU : U.card ≤ Nc) :
    (zeroCentres U).card ≤ zeroNcent Nc := by
  unfold zeroCentres
  simp only [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.card_singleton]
  have h3 : (({1, 2} : Finset ℝ)).card ≤ 2 := Finset.card_le_two
  have h4 : (sumCentresK U 6).card ≤ 7 ^ Nc :=
    (card_sumCentresK_le U _).trans (Nat.pow_le_pow_right (by omega) hU)
  calc _ ≤ 1 * (1 * (2 ^ 2 * ((7 ^ Nc) ^ 2 * (2 ^ 2 * (7 ^ Nc) ^ 2)))) := by gcongr
    _ = zeroNcent Nc := by unfold zeroNcent; ring

/-! ## The witnesses -/

/-- The common geometric facts used by the witnesses. -/
structure WitnessCtx (X : Finset Plane) (L Λ tol ρ cρ θ εc : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) (lab : Set ℂ → Plane × Plane) (Ucl : Finset ℂ)
    (Bad Fl : Finset (Set ℂ)) : Prop where
  hmk : IsMarking X L G mk
  hnoint : NoIntermediatePorts X L Λ G
  hlab : LabelledBy X tol G mk lab
  hcl : ∀ F ∈ exceptionalFaces X, F ∉ Bad → ∀ ab ∈ orientedSides X F,
    (∃ e ∈ unitEdges X, Sym2.map toC e = s(ab.1, ab.2) ∧ Λ ≤ trackLength X (allTrackOf X e)) →
    ∃ u ∈ Ucl, ‖(ab.2 - ab.1) - u‖ ≤ εc
  hclose : ∀ p ∈ ccwHullSides X, ∀ q ∈ ccwHullSides X, dist p.1 q.1 ≤ cρ * diam X →
    ‖toC (sideDir p) - toC (sideDir q)‖ ≤ ρ
  hmar : ∀ F ∈ G.good, F ∉ Fl → ∀ ab ∈ longSides X L F,
    ((ab.2 - ab.1) * conj (labDir lab F)).re ≤ -θ
  hθ : 0 < θ
  hρθ : ρ ≤ θ / 2
  hpar : 2 * (2 * tol * diam X + 1 + L) ≤ cρ * diam X
  hεc : 0 ≤ εc
  htol : 0 ≤ tol
  hL : 0 ≤ L

/-- The facts of the faces of a witness, given the context. -/
theorem witness_facts :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L Λ tol ρ cρ θ εc : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane) (Ucl : Finset ℂ) (Bad Fl : Finset (Set ℂ)),
      WitnessCtx X L Λ tol ρ cρ θ εc G mk lab Ucl Bad Fl →
      -- labels
      (∀ F ∈ G.good, ‖labDir lab F‖ = 1) ∧
      (∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        dist (lab q.1).1 (lab (trackMate X q).1).1 ≤ 2 * tol * diam X + 1 + L) ∧
      (∀ F ∈ G.good, ∀ F' ∈ G.good, dist (lab F).1 (lab F').1 ≤ cρ * diam X →
        ‖labDir lab F' - labDir lab F‖ ≤ ρ) ∧
      -- retained sums
      (∀ F ∈ G.good, ‖longSum X L F‖ ≤ 6) ∧
      (∀ F ∈ G.good, F ∉ Bad → ∃ z ∈ sumCentresK Ucl 6, ‖longSum X L F - z‖ ≤ 6 * εc) ∧
      (∀ F ∈ G.good, F ∉ Fl → ∀ ζ : ℂ, ‖labDir lab F - ζ‖ ≤ ρ →
        (longSum X L F * conj ζ).re ≤ -(θ / 2 * (longSides X L F).card)) := by
  filter_upwards [face_side_facts, mated_label_dist] with n hfacts hmld hfm X hX htri L Λ tol ρ
    cρ θ εc G mk lab Ucl Bad Fl hW
  have hccw : ∀ F ∈ G.good, lab F ∈ ccwHullSides X := fun F hF =>
    (Finset.mem_filter.1 (hW.hlab.2 F hF).1).1
  have hexF : ∀ F ∈ G.good, F ∈ exceptionalFaces X := fun F hF =>
    (mem_exceptionalFinset hX.1.2).1 (G.good_subset hF)
  have hcard6 : ∀ F ∈ G.good, (longSides X L F).card ≤ 6 := fun F hF =>
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (hfacts hfm X hX G F hF).1
  refine ⟨fun F hF => ?_, fun q hq hm => hmld hfm X hX htri L tol G mk lab hW.hlab q hq hm,
    fun F hF F' hF' hd => ?_, fun F hF => norm_longSum_le (hfacts hfm X hX G F hF).1
      (hfacts hfm X hX G F hF).2, fun F hF hFB => ?_, fun F hF hFl ζ hζ => ?_⟩
  · have hne : (lab F).1 ≠ (lab F).2 := (Finset.mem_filter.1 (hccw F hF)).2.2.2.1
    rw [labDir, LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
  · refine hW.hclose _ (hccw F' hF') _ (hccw F hF) ?_
    rw [dist_comm]; exact hd
  · have hlongcl : ∀ ab ∈ longSides X L F, ∃ u ∈ Ucl, ‖(ab.2 - ab.1) - u‖ ≤ εc := by
      intro ab hab
      obtain ⟨e', he', hmap, hport', hlong⟩ := longSide_edge (hexF F hF) hab
      refine hW.hcl F (hexF F hF) hFB ab (Finset.mem_filter.1 hab).1 ⟨e', he', hmap, ?_⟩
      rcases hW.hnoint F hF e' he' hport' with h | h
      · exact absurd h hlong
      · exact h
    have := sum_near_sumCentresK (longSides X L F) (fun ab => ab.2 - ab.1) Ucl (K := 6) hW.hεc
      (hcard6 F hF) hlongcl
    simpa [longSum] using this
  · refine re_longSum_le fun ab hab => ?_
    have hu : ‖ab.2 - ab.1‖ = 1 := (hfacts hfm X hX G F hF).2 ab (Finset.mem_filter.1 hab).1
    have := re_shift hu (hW.hmar F hF hFl ab hab) hζ
    linarith [hW.hρθ]

/-- The relation at a degree-two neighbour, with the label direction replaced by `ζ`. -/
theorem H_relation :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol ρ : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane) (ζ : ℂ), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good →
        ‖labDir lab (trackMate X q).1 - ζ‖ ≤ ρ →
        ∃ u : ℂ, ‖u‖ = 1 ∧ ‖(G.kMult (trackMate X q).1 : ℂ) * ζ + longSum X L (trackMate X q).1 -
          portVec X q + u‖ ≤ tol + 2 * ρ := by
  filter_upwards [ext_H_equation] with n hHeq hfm X hX htri L tol ρ G mk lab ζ hmk hlab q hq hm
    hH hl
  obtain ⟨u, hu, hE⟩ := hHeq hfm X hX htri L tol G mk lab hmk hlab q hq hm hH
  refine ⟨u, hu, ?_⟩
  have h := kmul_repl (G.kMult_cases (trackMate X q).1)
    (x := longSum X L (trackMate X q).1 - portVec X q + u) hl
  have e1 : (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 +
      (longSum X L (trackMate X q).1 - portVec X q + u) =
      (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 - portVec X q + u +
        longSum X L (trackMate X q).1 := by ring
  have e2 : (G.kMult (trackMate X q).1 : ℂ) * ζ + longSum X L (trackMate X q).1 -
      portVec X q + u = (G.kMult (trackMate X q).1 : ℂ) * ζ +
        (longSum X L (trackMate X q).1 - portVec X q + u) := by ring
  rw [e1] at h
  rw [e2]
  linarith

lemma kMult_mem (G : GoodFaces X) (F : Set ℂ) : G.kMult F ∈ ({1, 2} : Set ℝ) := by
  rcases G.kMult_cases F with h | h <;> simp [h]

lemma kMult_mem' (G : GoodFaces X) (F : Set ℂ) : G.kMult F ∈ ({1, 2} : Finset ℝ) := by
  rcases G.kMult_cases F with h | h <;> simp [h]

set_option maxHeartbeats 1000000 in
/-- **The witness of §13.2.** -/
theorem defJ_witness :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L Λ tol ρ cρ θ εc μ0 r0 : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane) (Ucl : Finset ℂ) (Bad Fl : Finset (Set ℂ)),
      WitnessCtx X L Λ tol ρ cρ θ εc G mk lab Ucl Bad Fl →
      2 * tol + 2 * ρ < r0 → 6 * εc < μ0 →
      ∀ q1 ∈ unmarkedPorts X L G mk, ∀ q2 ∈ unmarkedPorts X L G mk, q1.1 = q2.1 → q1 ≠ q2 →
        (trackGraph X L G mk).deg q1.1 = 3 → q1.1 ∉ Fl → q1.1 ∉ Bad →
        TrackMated X L G mk q1 → TrackMated X L G mk q2 →
        (trackMate X q1).1 ∈ (trackGraph X L G mk).Hs G.good →
        (trackMate X q2).1 ∈ (trackGraph X L G mk).Hs G.good →
        (trackMate X q1).1 ∉ Fl → (trackMate X q2).1 ∉ Fl →
        (trackMate X q1).1 ∉ Bad → (trackMate X q2).1 ∉ Bad →
        ∃ d ∈ defJAdm 6 (θ / 2), (∃ c ∈ zeroCentres Ucl, ‖d - c‖ < μ0) ∧
          CapApproxK 2 r0 defJB d (labDir lab q1.1) := by
  filter_upwards [witness_facts, J_ports_equation, H_relation, portVec_unit, card_longSides_J] with
    n hfacts hJeq hHrel hunit hJc hfm X hX htri L Λ tol ρ cρ θ εc μ0 r0 G mk lab Ucl Bad Fl hW hr0
    hμ0 q1 hq1 q2 hq2 h12 hne hdeg hFl hFB hm1 hm2 hH1 hH2 hH1l hH2l hH1B hH2B
  obtain ⟨hτu, hmd, hloc, hZ6, hcen, hre⟩ :=
    hfacts hfm X hX htri L Λ tol ρ cρ θ εc G mk lab Ucl Bad Fl hW
  have hFg : q1.1 ∈ G.good := (mem_unmarkedPorts.1 hq1).1
  have hH1g : (trackMate X q1).1 ∈ G.good := (Finset.mem_filter.1 hH1).1
  have hH2g : (trackMate X q2).1 ∈ G.good := (Finset.mem_filter.1 hH2).1
  have hD0 : 0 ≤ diam X := Metric.diam_nonneg
  have hδ : 2 * tol * diam X + 1 + L ≤ cρ * diam X := by
    have := hW.hpar; have := hW.htol; have := hW.hL
    have : 0 ≤ 2 * tol * diam X := by positivity
    linarith
  have hl1 : ‖labDir lab (trackMate X q1).1 - labDir lab q1.1‖ ≤ ρ :=
    hloc _ hFg _ hH1g ((hmd q1 hq1 hm1).trans hδ)
  have hl2 : ‖labDir lab (trackMate X q2).1 - labDir lab q1.1‖ ≤ ρ := by
    refine hloc _ hFg _ hH2g ?_
    have := hmd q2 hq2 hm2
    rw [← h12] at this
    exact this.trans hδ
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hl1
  have htol0 := hW.htol
  have hτ := hτu _ hFg
  obtain ⟨s3, hs3, hJ⟩ := hJeq hfm X hX htri L tol G mk lab hW.hmk hW.hlab q1 hq1 q2 hq2 h12 hdeg
    hne
  obtain ⟨u1, hu1, hE1⟩ := hHrel hfm X hX htri L tol ρ G mk lab (labDir lab q1.1) hW.hmk hW.hlab
    q1 hq1 hm1 hH1 hl1
  obtain ⟨u2, hu2, hE2⟩ := hHrel hfm X hX htri L tol ρ G mk lab (labDir lab q1.1) hW.hmk hW.hlab
    q2 hq2 hm2 hH2 hl2
  have hs1 := hunit hfm X hX L G mk q1 hq1
  have hs2 := hunit hfm X hX L G mk q2 hq2
  -- the margins
  have hc1 := hJc hfm X hX htri L G mk hW.hmk _ hFg hdeg
  have hreF := hre _ hFg hFl (labDir lab q1.1) (by rw [sub_self, norm_zero]; exact hρ0)
  rw [hc1, Nat.cast_one, mul_one] at hreF
  have hre1 := hre _ hH1g hH1l _ hl1
  have hre2 := hre _ hH2g hH2l _ hl2
  have hθ := hW.hθ
  have hp1 : 0 ≤ θ / 2 * ((longSides X L (trackMate X q1).1).card : ℝ) := by positivity
  have hp2 : 0 ≤ θ / 2 * ((longSides X L (trackMate X q2).1).card : ℝ) := by positivity
  -- the centres
  obtain ⟨zF, hzF, hzFd⟩ := hcen _ hFg hFB
  obtain ⟨z1, hz1, hz1d⟩ := hcen _ hH1g hH1B
  obtain ⟨z2, hz2, hz2d⟩ := hcen _ hH2g hH2B
  have hμ : 0 < μ0 := by linarith [hW.hεc]
  refine ⟨((0 : ℝ), (0 : ℂ), ![G.kMult q1.1, G.kMult (trackMate X q2).1],
    ![longSum X L q1.1, longSum X L (trackMate X q2).1], ![G.kMult (trackMate X q1).1, 1],
    ![longSum X L (trackMate X q1).1, 0]), ⟨⟨Set.mem_singleton _, Set.mem_singleton _, ?_, ?_, ?_,
      ?_⟩, ?_, ?_, ?_, ?_⟩, ⟨((0 : ℝ), (0 : ℂ), ![G.kMult q1.1, G.kMult (trackMate X q2).1],
    ![zF, z2], ![G.kMult (trackMate X q1).1, 1], ![z1, 0]), ?_, ?_⟩,
    ⟨![-portVec X q2, portVec X q2], ![s3, u2], ![portVec X q1, 1], ![u1, 1], ?_, ?_, ?_⟩⟩
  · intro i _; fin_cases i <;> simp [GoodFaces.kMult_cases]
  · intro i _; fin_cases i <;> simp [hZ6 _ hFg, hZ6 _ hH2g]
  · intro i _; fin_cases i <;> simp [GoodFaces.kMult_cases]
  · intro i _; fin_cases i <;> simp [hZ6 _ hH1g]
  · show θ / 2 ≤ ‖longSum X L q1.1‖
    exact norm_ge_of_re_le hτ hreF
  · show θ / 2 ≤ ‖longSum X L q1.1 + longSum X L (trackMate X q1).1‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, Complex.add_re]; linarith
  · show θ / 2 ≤ ‖longSum X L q1.1 + longSum X L (trackMate X q2).1‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, Complex.add_re]; linarith
  · show θ / 2 ≤ ‖longSum X L q1.1 + longSum X L (trackMate X q1).1 +
      longSum X L (trackMate X q2).1‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, add_mul, Complex.add_re, Complex.add_re]; linarith
  · simp only [zeroCentres, Finset.mem_product, Finset.mem_singleton, Fintype.mem_piFinset,
      Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨trivial, trivial, ⟨kMult_mem' _ _, kMult_mem' _ _⟩, ⟨hzF, hz2⟩, ⟨kMult_mem' _ _, by simp⟩,
      ⟨hz1, zero_mem_sumCentresK _ _⟩⟩
  · refine capDataK_norm_lt hμ rfl (by simpa using hμ) rfl (fun i => ?_) rfl (fun i => ?_)
    · fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.head_cons]; linarith
    · fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
      · simp [hμ]
  · intro i; fin_cases i <;> simp [hs1, hs2, hs3, hu1, hu2]
  · simp [capRes0K, Fin.sum_univ_two]; linarith
  · intro i
    fin_cases i
    · simp only [capRes1K, defJB, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.val_zero,
        decide_true, if_true]
      have e : ((G.kMult q1.1 : ℝ) : ℂ) * labDir lab q1.1 + longSum X L q1.1 - -portVec X q2 +
          portVec X q1 + s3 = (G.kMult q1.1 : ℂ) * labDir lab q1.1 + portVec X q1 +
            portVec X q2 + s3 + longSum X L q1.1 := by ring
      rw [e]; linarith
    · simp only [capRes1K, defJB, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.head_cons, Fin.val_one, one_ne_zero, decide_false,
        Bool.false_eq_true, if_false]
      linarith

set_option maxHeartbeats 1000000 in
/-- **The witness of §13.3.** -/
theorem jj_witness :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L Λ tol ρ cρ θ εc μ0 r0 : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane) (Ucl : Finset ℂ) (Bad Fl : Finset (Set ℂ)),
      WitnessCtx X L Λ tol ρ cρ θ εc G mk lab Ucl Bad Fl →
      2 * tol + 4 * ρ < r0 → 6 * εc < μ0 →
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        q.1 ∈ (trackGraph X L G mk).Js G.good → (trackMate X q).1 ∈ (trackGraph X L G mk).Js G.good →
        q.1 ∉ Fl → (trackMate X q).1 ∉ Fl → q.1 ∉ Bad → (trackMate X q).1 ∉ Bad →
      ∀ q1 ∈ unmarkedPorts X L G mk, q1.1 = q.1 → TrackMated X L G mk q1 →
        (trackMate X q1).1 ∈ (trackGraph X L G mk).Hs G.good → (trackMate X q1).1 ∉ Fl →
        (trackMate X q1).1 ∉ Bad →
      ∀ q2 ∈ unmarkedPorts X L G mk, q2.1 = (trackMate X q).1 → TrackMated X L G mk q2 →
        (trackMate X q2).1 ∈ (trackGraph X L G mk).Hs G.good → (trackMate X q2).1 ∉ Fl →
        (trackMate X q2).1 ∉ Bad →
        ∃ d ∈ jjAdm 6 (θ / 2), (∃ c ∈ zeroCentres Ucl, ‖d - c‖ < μ0) ∧
          CapApproxK 2 r0 (fun _ => true) d (labDir lab q.1) := by
  filter_upwards [witness_facts, J_ports_equation, ext_J_equation, H_relation, portVec_unit,
    card_longSides_J, card_trackEnds] with n hfacts hJeq hJext hHrel hunit hJc hends hfm X hX htri
    L Λ tol ρ cρ θ εc μ0 r0 G mk lab Ucl Bad Fl hW hr0 hμ0 q hq hm hJ1 hJ2 hF1l hF2l hF1B hF2B
    q1 hq1 hq11 hm1 hH1 hH1l hH1B q2 hq2 hq21 hm2 hH2 hH2l hH2B
  obtain ⟨hτu, hmd, hloc, hZ6, hcen, hre⟩ :=
    hfacts hfm X hX htri L Λ tol ρ cρ θ εc G mk lab Ucl Bad Fl hW
  have hM := trackMate_isMatching (hends hfm X hX htri) L G mk
  have hF1g : q.1 ∈ G.good := (Finset.mem_filter.1 hJ1).1
  have hF2g : (trackMate X q).1 ∈ G.good := (Finset.mem_filter.1 hJ2).1
  have hH1g : (trackMate X q1).1 ∈ G.good := (Finset.mem_filter.1 hH1).1
  have hH2g : (trackMate X q2).1 ∈ G.good := (Finset.mem_filter.1 hH2).1
  have hdeg1 : (trackGraph X L G mk).deg q.1 = 3 := (Finset.mem_filter.1 hJ1).2.1
  have hdeg2 : (trackGraph X L G mk).deg (trackMate X q).1 = 3 := (Finset.mem_filter.1 hJ2).2.1
  have hD0 : 0 ≤ diam X := Metric.diam_nonneg
  have htol0 := hW.htol
  have hpar := hW.hpar
  have hδ0 : 0 ≤ 2 * tol * diam X + 1 + L := by have := hW.hL; positivity
  have hd12 := hmd q hq hm
  have hd1H := hmd q1 hq1 hm1
  rw [hq11] at hd1H
  have hd2H := hmd q2 hq2 hm2
  rw [hq21] at hd2H
  have hl2 : ‖labDir lab (trackMate X q).1 - labDir lab q.1‖ ≤ ρ :=
    hloc _ hF1g _ hF2g (by linarith)
  have hl1 : ‖labDir lab (trackMate X q1).1 - labDir lab q.1‖ ≤ ρ :=
    hloc _ hF1g _ hH1g (by linarith)
  have hl2' : ‖labDir lab (trackMate X q2).1 - labDir lab q.1‖ ≤ ρ := by
    refine hloc _ hF1g _ hH2g ?_
    have := dist_triangle (lab q.1).1 (lab (trackMate X q).1).1 (lab (trackMate X q2).1).1
    linarith
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hl1
  have hτ := hτu _ hF1g
  -- distinct ports
  have hne1 : q ≠ q1 := by
    intro h
    rw [← h] at hH1
    exact Hs_Js_disjoint hH1 hJ2
  have hne2 : q2 ≠ trackMate X q := by
    intro h
    have h' : (trackMate X q2).1 = q.1 := by rw [h, (hM q hq hm).2.2.1]
    rw [h'] at hH2
    exact Hs_Js_disjoint hH2 hJ1
  -- the relations
  obtain ⟨r1, hr1, hE0⟩ := hJeq hfm X hX htri L tol G mk lab hW.hmk hW.hlab q hq q1 hq1 hq11.symm
    hdeg1 hne1
  obtain ⟨r2, hr2, hE0'⟩ := hJext hfm X hX htri L tol G mk lab hW.hmk hW.hlab q hq hm hdeg2 q2 hq2
    hq21 hne2
  obtain ⟨u1, hu1, hE1⟩ := hHrel hfm X hX htri L tol ρ G mk lab (labDir lab q.1) hW.hmk hW.hlab
    q1 hq1 hm1 hH1 hl1
  obtain ⟨u2, hu2, hE2⟩ := hHrel hfm X hX htri L tol ρ G mk lab (labDir lab q.1) hW.hmk hW.hlab
    q2 hq2 hm2 hH2 hl2'
  have hE0'' : ‖(G.kMult (trackMate X q).1 : ℂ) * labDir lab q.1 +
      longSum X L (trackMate X q).1 - portVec X q + portVec X q2 + r2‖ ≤ tol + 2 * ρ := by
    have h := kmul_repl (G.kMult_cases (trackMate X q).1)
      (x := -portVec X q + portVec X q2 + r2 + longSum X L (trackMate X q).1) hl2
    have e1 : (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 +
        (-portVec X q + portVec X q2 + r2 + longSum X L (trackMate X q).1) =
        (G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 - portVec X q +
          portVec X q2 + r2 + longSum X L (trackMate X q).1 := by ring
    have e2 : (G.kMult (trackMate X q).1 : ℂ) * labDir lab q.1 +
        longSum X L (trackMate X q).1 - portVec X q + portVec X q2 + r2 =
        (G.kMult (trackMate X q).1 : ℂ) * labDir lab q.1 +
          (-portVec X q + portVec X q2 + r2 + longSum X L (trackMate X q).1) := by ring
    rw [e1] at h
    rw [e2]
    linarith
  have hs := hunit hfm X hX L G mk q hq
  have hs1 := hunit hfm X hX L G mk q1 hq1
  have hs2 := hunit hfm X hX L G mk q2 hq2
  -- the margins
  have hc1 := hJc hfm X hX htri L G mk hW.hmk _ hF1g hdeg1
  have hc2 := hJc hfm X hX htri L G mk hW.hmk _ hF2g hdeg2
  have hreF1 := hre _ hF1g hF1l (labDir lab q.1) (by rw [sub_self, norm_zero]; exact hρ0)
  rw [hc1, Nat.cast_one, mul_one] at hreF1
  have hreF2 := hre _ hF2g hF2l _ hl2
  rw [hc2, Nat.cast_one, mul_one] at hreF2
  have hre1 := hre _ hH1g hH1l _ hl1
  have hre2 := hre _ hH2g hH2l _ hl2'
  have hθ := hW.hθ
  have hp1 : 0 ≤ θ / 2 * ((longSides X L (trackMate X q1).1).card : ℝ) := by positivity
  have hp2 : 0 ≤ θ / 2 * ((longSides X L (trackMate X q2).1).card : ℝ) := by positivity
  -- the centres
  obtain ⟨zF1, hzF1, hzF1d⟩ := hcen _ hF1g hF1B
  obtain ⟨zF2, hzF2, hzF2d⟩ := hcen _ hF2g hF2B
  obtain ⟨z1, hz1, hz1d⟩ := hcen _ hH1g hH1B
  obtain ⟨z2, hz2, hz2d⟩ := hcen _ hH2g hH2B
  have hμ : 0 < μ0 := by linarith [hW.hεc]
  refine ⟨((0 : ℝ), (0 : ℂ), ![G.kMult q.1, G.kMult (trackMate X q).1],
    ![longSum X L q.1, longSum X L (trackMate X q).1],
    ![G.kMult (trackMate X q1).1, G.kMult (trackMate X q2).1],
    ![longSum X L (trackMate X q1).1, longSum X L (trackMate X q2).1]),
    ⟨⟨Set.mem_singleton _, Set.mem_singleton _, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨((0 : ℝ), (0 : ℂ), ![G.kMult q.1, G.kMult (trackMate X q).1], ![zF1, zF2],
      ![G.kMult (trackMate X q1).1, G.kMult (trackMate X q2).1], ![z1, z2]), ?_, ?_⟩,
    ⟨![-portVec X q, portVec X q], ![r1, r2], ![portVec X q1, portVec X q2], ![u1, u2], ?_, ?_,
      ?_⟩⟩
  · intro i _; fin_cases i <;> simp [GoodFaces.kMult_cases]
  · intro i _; fin_cases i <;> simp [hZ6 _ hF1g, hZ6 _ hF2g]
  · intro i _; fin_cases i <;> simp [GoodFaces.kMult_cases]
  · intro i _; fin_cases i <;> simp [hZ6 _ hH1g, hZ6 _ hH2g]
  · show θ / 2 ≤ ‖longSum X L q.1‖
    exact norm_ge_of_re_le hτ hreF1
  · show θ / 2 ≤ ‖longSum X L q.1 + longSum X L (trackMate X q1).1‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, Complex.add_re]; linarith
  · show θ / 2 ≤ ‖longSum X L (trackMate X q).1‖
    exact norm_ge_of_re_le hτ hreF2
  · show θ / 2 ≤ ‖longSum X L (trackMate X q).1 + longSum X L (trackMate X q2).1‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, Complex.add_re]; linarith
  · show θ / 2 ≤ ‖longSum X L q.1 + longSum X L (trackMate X q).1‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, Complex.add_re]; linarith
  · show θ / 2 ≤ ‖longSum X L q.1 + longSum X L (trackMate X q1).1 +
      longSum X L (trackMate X q).1‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, add_mul, Complex.add_re, Complex.add_re]; linarith
  · show θ / 2 ≤ ‖longSum X L q.1 + (longSum X L (trackMate X q).1 +
      longSum X L (trackMate X q2).1)‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, add_mul, Complex.add_re, Complex.add_re]; linarith
  · show θ / 2 ≤ ‖longSum X L q.1 + longSum X L (trackMate X q1).1 +
      (longSum X L (trackMate X q).1 + longSum X L (trackMate X q2).1)‖
    refine norm_ge_of_re_le hτ ?_
    rw [add_mul, add_mul, add_mul, Complex.add_re, Complex.add_re, Complex.add_re]; linarith
  · simp only [zeroCentres, Finset.mem_product, Finset.mem_singleton, Fintype.mem_piFinset,
      Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨trivial, trivial, ⟨kMult_mem' _ _, kMult_mem' _ _⟩, ⟨hzF1, hzF2⟩,
      ⟨kMult_mem' _ _, kMult_mem' _ _⟩, ⟨hz1, hz2⟩⟩
  · refine capDataK_norm_lt hμ rfl (by simpa using hμ) rfl (fun i => ?_) rfl (fun i => ?_)
    · fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.head_cons]; linarith
    · fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.head_cons]; linarith
  · intro i; fin_cases i <;> simp [hs, hs1, hs2, hr1, hr2, hu1, hu2]
  · simp [capRes0K, Fin.sum_univ_two]; linarith
  · intro i
    fin_cases i
    · simp only [capRes1K, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, if_true]
      have e : ((G.kMult q.1 : ℝ) : ℂ) * labDir lab q.1 + longSum X L q.1 - -portVec X q +
          portVec X q1 + r1 = (G.kMult q.1 : ℂ) * labDir lab q.1 + portVec X q +
            portVec X q1 + r1 + longSum X L q.1 := by ring
      rw [e]; linarith
    · simp only [capRes1K, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, if_true]
      linarith

end Erdos99
end

end FlaggedGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FlaggedCount`
-/

section FlaggedCount

/-!
# Counting the defective `J` faces and the exceptional `J–J` edges (§§13.2–13.3)

* `StubGraph.inc_ofHalfEdges_le`, `StubGraph.card_E_filter_le`: incidences and edges of a graph
  built from half-edges are bounded by the corresponding half-edges;
* `card_le_three_mul_image`: half-edges at degree-three faces number at most three times their
  faces;
* `defJ_count` (§13.2) and `excE_count` (§13.3): the algebraic exclusion steps with the unflagged
  margin as hypothesis: the defective `J` faces and the exceptional `J–J` edges are few.
-/

open scoped BigOperators Real
open Filter ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim CaplessKElim

namespace LocalCharge.StubGraph

variable {α β : Type*} [Inhabited β] {P : Finset β} {v : β → α} {mate : β → β}
  {mated : β → Prop}

open LocalCharge.StubGraph

lemma mem_ofHalfEdges_E {i : ℕ} : i ∈ (ofHalfEdges P v mate mated).E ↔
    i < P.card ∧ mated (hEnum P i) ∧ i < hIdx P (mate (hEnum P i)) := by
  simp [ofHalfEdges]

/-- Edges satisfying a property of their ends are bounded by matched half-edges with the property. -/
theorem card_E_filter_le (p : α → α → Prop) :
    ((ofHalfEdges P v mate mated).E.filter (fun e =>
      p ((ofHalfEdges P v mate mated).src e) ((ofHalfEdges P v mate mated).tgt e))).card ≤
      (P.filter (fun q => mated q ∧ p (v q) (v (mate q)))).card := by
  refine Finset.card_le_card_of_injOn (hEnum P) (fun i hi => ?_) (fun i hi j hj h => ?_)
  · obtain ⟨hiE, hp⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    obtain ⟨h1, h2, -⟩ := mem_ofHalfEdges_E.1 hiE
    exact Finset.mem_filter.2 ⟨hEnum_mem P h1, h2, hp⟩
  · have hi' := (mem_ofHalfEdges_E.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1).1
    have hj' := (mem_ofHalfEdges_E.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1).1
    rw [← hIdx_hEnum P hi', ← hIdx_hEnum P hj']
    exact congrArg (hIdx P) h

/-- Incidences of a vertex are bounded by its matched half-edges with mate in `B`. -/
theorem inc_ofHalfEdges_le (hM : IsMatching P mate mated) (a : α) (B : Finset α) :
    (ofHalfEdges P v mate mated).inc a B ≤
      (P.filter (fun q => v q = a ∧ mated q ∧ v (mate q) ∈ B)).card := by
  set S1 := P.filter (fun q => (v q = a ∧ mated q ∧ v (mate q) ∈ B) ∧
    hIdx P q < hIdx P (mate q)) with hS1
  set S2 := P.filter (fun q => (v q = a ∧ mated q ∧ v (mate q) ∈ B) ∧
    hIdx P (mate q) < hIdx P q) with hS2
  have h1 : ((ofHalfEdges P v mate mated).E.filter (fun e =>
      (ofHalfEdges P v mate mated).src e = a ∧ (ofHalfEdges P v mate mated).tgt e ∈ B)).card ≤
      S1.card := by
    refine Finset.card_le_card_of_injOn (hEnum P) (fun i hi => ?_) (fun i hi j hj h => ?_)
    · obtain ⟨hiE, hs, ht⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
      obtain ⟨h1, h2, h3⟩ := mem_ofHalfEdges_E.1 hiE
      refine Finset.mem_filter.2 ⟨hEnum_mem P h1, ⟨hs, h2, ht⟩, ?_⟩
      rw [hIdx_hEnum P h1]; exact h3
    · have hi' := (mem_ofHalfEdges_E.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1).1
      have hj' := (mem_ofHalfEdges_E.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1).1
      rw [← hIdx_hEnum P hi', ← hIdx_hEnum P hj']
      exact congrArg (hIdx P) h
  have h2 : ((ofHalfEdges P v mate mated).E.filter (fun e =>
      (ofHalfEdges P v mate mated).tgt e = a ∧ (ofHalfEdges P v mate mated).src e ∈ B)).card ≤
      S2.card := by
    refine Finset.card_le_card_of_injOn (fun i => mate (hEnum P i)) (fun i hi => ?_)
      (fun i hi j hj h => ?_)
    · obtain ⟨hiE, ht, hs⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
      obtain ⟨h1, h2, h3⟩ := mem_ofHalfEdges_E.1 hiE
      have hm := hEnum_mem P h1
      obtain ⟨hm1, -, hm3, hm4⟩ := hM _ hm h2
      refine Finset.mem_filter.2 ⟨hm1, ⟨ht, hm4, ?_⟩, ?_⟩
      · rw [hm3]; exact hs
      · rw [hm3, hIdx_hEnum P h1]; exact h3
    · have hi' := mem_ofHalfEdges_E.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
      have hj' := mem_ofHalfEdges_E.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
      have e1 := (hM _ (hEnum_mem P hi'.1) hi'.2.1).2.2.1
      have e2 := (hM _ (hEnum_mem P hj'.1) hj'.2.1).2.2.1
      have h' : hEnum P i = hEnum P j := by
        rw [← e1, ← e2]; exact congrArg mate h
      rw [← hIdx_hEnum P hi'.1, ← hIdx_hEnum P hj'.1, h']
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact lt_asymm (Finset.mem_filter.1 h1).2.2 (Finset.mem_filter.1 h2).2.2
  have hsub : S1 ∪ S2 ⊆ P.filter (fun q => v q = a ∧ mated q ∧ v (mate q) ∈ B) := by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h).1, (Finset.mem_filter.1 h).2.1⟩
    · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h).1, (Finset.mem_filter.1 h).2.1⟩
  unfold inc
  calc _ ≤ S1.card + S2.card := add_le_add h1 h2
    _ = (S1 ∪ S2).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

end LocalCharge.StubGraph

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

/-- Incidences in the track graph are bounded by matched ports. -/
lemma trackGraph_inc_le (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (F : Set ℂ)
    (B : Finset (Set ℂ)) :
    (trackGraph X L G mk).inc F B ≤ ((unmarkedPorts X L G mk).filter (fun q =>
      q.1 = F ∧ TrackMated X L G mk q ∧ (trackMate X q).1 ∈ B)).card :=
  LocalCharge.StubGraph.inc_ofHalfEdges_le (trackMate_isMatching hends L G mk) F B

/-- Half-edges at degree-three faces number at most three times their faces. -/
lemma card_le_three_mul_image (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {S : Finset (Set ℂ × Sym2 Plane)} (hS : S ⊆ unmarkedPorts X L G mk)
    (h3 : ∀ q ∈ S, (trackGraph X L G mk).deg q.1 = 3) :
    S.card ≤ 3 * (S.image Prod.fst).card := by
  have hM := trackMate_isMatching hends L G mk
  refine Finset.card_le_mul_card_image S 3 fun F hF => ?_
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hF
  have hdeg := h3 q hq
  rw [trackGraph, StubGraph.deg_ofHalfEdges hM] at hdeg
  rw [← hdeg]
  refine Finset.card_le_card fun q' hq' => ?_
  obtain ⟨hq'S, hq'1⟩ := Finset.mem_filter.1 hq'
  exact Finset.mem_filter.2 ⟨hS hq'S, hq'1⟩

lemma mem_badMates {Bad : Finset (Set ℂ)} {q : Set ℂ × Sym2 Plane}
    (hq : q ∈ unmarkedPorts X L G mk) (hm : TrackMated X L G mk q) (hB : (trackMate X q).1 ∈ Bad) :
    q.1 ∈ badMates X L G mk Bad :=
  Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hq, hm, hB⟩, rfl⟩

/-- The source labels of `HasUnflaggedMargin` and the margin of the long sides. -/
lemma HasUnflaggedMargin.labelledBy (hX : IsSeparated X) {θ tol : ℝ} {Fl : Finset (Set ℂ)}
    (h : HasUnflaggedMargin X L θ tol G mk Fl) :
    ∃ lab, LabelledBy X tol G mk lab ∧ ∀ F ∈ G.good, F ∉ Fl → ∀ ab ∈ longSides X L F,
      ((ab.2 - ab.1) * conj (labDir lab F)).re ≤ -θ := by
  obtain ⟨lab, hinj, hl⟩ := h
  refine ⟨lab, ⟨hinj, fun F hF => ⟨(hl F hF).1, (hl F hF).2.1, (hl F hF).2.2.1⟩⟩,
    fun F hF hFl ab hab => ?_⟩
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX).1 (G.good_subset hF)
  obtain ⟨e, he, hmap, hport, hlong⟩ := longSide_edge hFe hab
  have := (hl F hF).2.2.2 hFl ab (Finset.mem_filter.1 hab).1 e he hport hmap (not_lt.1 hlong)
  rw [inner_eq_re_mul_conj] at this
  exact this.le

set_option maxHeartbeats 1000000 in
/-- **§13.2, the algebraic exclusion step with the margin as hypothesis**: the defective `J` faces
(unflagged, with two incidences to unflagged degree-two faces) are few. -/
theorem defJ_count {ε lam θ : ℝ} (hε : 0 < ε) (hlam : 0 < lam) (hθ : 0 < θ) :
    ∃ ρ, 0 < ρ ∧ ∃ tol, 0 < tol ∧ ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, IsRoundCentre ρ X O →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → NoIntermediatePorts X (a * diam X) (lam * diam X) G →
          ∀ Fl : Finset (Set ℂ), HasUnflaggedMargin X (a * diam X) θ tol G mk Fl →
          qDefJ X (a * diam X) G mk Fl ≤ ε * diam X := by
  obtain ⟨Nc, hclus⟩ := long_sides_clustered hlam
  obtain ⟨r0, hr0, μ0, hμ0, hfew⟩ := directions_few_of_exact 2 defJB (isCompact_defJAdm 6 (θ / 2))
    (capDegK 2) (fun d hd => defJ_exact_card_le 6 (half_pos hθ) hd) (zeroNcent Nc)
    (ε := ε / 8) (by positivity)
  set ρ : ℝ := min (θ / 2) (r0 / 8) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρθ : ρ ≤ θ / 2 := min_le_left _ _
  have hρr : ρ ≤ r0 / 8 := min_le_right _ _
  obtain ⟨cρ, hcρ, hclose⟩ := labDir_close hρ
  set εc : ℝ := μ0 / 7 with hεcdef
  have hεc : 0 < εc := by positivity
  obtain ⟨Mb, hclusM⟩ := hclus εc hεc
  set t0 : ℝ := min ρ (cρ / 8) with ht0def
  have ht0 : 0 < t0 := lt_min hρ (by positivity)
  have ht0ρ : t0 ≤ ρ := min_le_left _ _
  have ht0c : t0 ≤ cρ / 8 := min_le_right _ _
  refine ⟨1, one_pos, t0, ht0, cρ / 8, by positivity, fun a ha hab => ?_⟩
  filter_upwards [hfew, hclose, hclusM, defJ_witness, card_trackEnds,
    eventually_diam_ge (40 * |Mb| / ε), eventually_diam_ge (16 / cρ), eventually_diam_ge 1] with
    n hfewn hclosen hclusn hwit hends hDbig hDbig2 hD1
  intro hfm X hX htri O _ G mk hmk hwin hnoint Fl hmarg
  have hD : 0 < diam X := lt_of_lt_of_le one_pos (hD1 X hX)
  set D := diam X with hDdef
  set Lc := a * D with hLc
  obtain ⟨lab, hlab, hmarF⟩ := hmarg.labelledBy hX.1.2
  obtain ⟨Ucl, hUcl, Bad, hBad, hcl⟩ := hclusn hfm X hX htri
  have hends' := hends hfm X hX htri
  have hpar : 2 * (2 * t0 * D + 1 + Lc) ≤ cρ * D := by
    have h1 : 16 ≤ cρ * D := by
      have := hDbig2 X hX; rw [div_le_iff₀ hcρ] at this; linarith
    have h2 : t0 * D ≤ cρ / 8 * D := mul_le_mul_of_nonneg_right ht0c hD.le
    have h3 : a * D ≤ cρ / 8 * D := mul_le_mul_of_nonneg_right hab hD.le
    nlinarith
  have hW : WitnessCtx X Lc (lam * D) t0 ρ cρ θ εc G mk lab Ucl Bad Fl :=
    ⟨hmk, hnoint, hlab, hcl, hclosen X hX, hmarF, hθ, hρθ, hpar, hεc.le, ht0.le, by positivity⟩
  have hr1 : 2 * t0 + 2 * ρ < r0 := by linarith
  have hμ1 : 6 * εc < μ0 := by rw [hεcdef]; linarith
  -- the defective faces
  set Dset := ((trackGraph X Lc G mk).Js G.good).filter (fun F => F ∉ Fl ∧
    2 ≤ (trackGraph X Lc G mk).inc F ((trackGraph X Lc G mk).Hs G.good \ Fl)) with hDset
  set Bad' := Bad ∪ badMates X Lc G mk Bad with hBad'
  have hBad'card : Bad'.card ≤ 5 * Bad.card := by
    show (Bad ∪ badMates X Lc G mk Bad).card ≤ 5 * Bad.card
    have := card_badMates_le hends' hmk hwin Bad
    have := Finset.card_union_le Bad (badMates X Lc G mk Bad)
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := Dset) (fun F => F ∈ Bad')
  have hExc : (Dset.filter (fun F => F ∈ Bad')).card ≤ Bad'.card :=
    Finset.card_le_card fun F hF => (Finset.mem_filter.1 hF).2
  set Rest := Dset.filter (fun F => F ∉ Bad') with hRest
  have hRestgood : Rest ⊆ G.good := fun F hF =>
    (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hF).1).1).1
  have hinj : Set.InjOn lab Rest := hlab.1.mono hRestgood
  have hA := hfewn X hX (zeroCentres Ucl) (card_zeroCentres_le hUcl) (Rest.image lab)
    (fun p hp => by
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 (hlab.2 F (hRestgood hF)).1).1)
    (fun p hp => by
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hFD, hFB'⟩ := Finset.mem_filter.1 hF
      obtain ⟨hFJ, hFl, h2⟩ := Finset.mem_filter.1 hFD
      have hc := h2.trans (trackGraph_inc_le hends' F _)
      obtain ⟨q1, hq1, q2, hq2, hne⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le one_lt_two hc)
      obtain ⟨hq1P, hq1F, hm1, hH1⟩ := Finset.mem_filter.1 hq1
      obtain ⟨hq2P, hq2F, hm2, hH2⟩ := Finset.mem_filter.1 hq2
      obtain ⟨hH1H, hH1l⟩ := Finset.mem_sdiff.1 hH1
      obtain ⟨hH2H, hH2l⟩ := Finset.mem_sdiff.1 hH2
      have hFB : F ∉ Bad := fun h => hFB' (Finset.mem_union_left _ h)
      have hB1 : (trackMate X q1).1 ∉ Bad := fun h =>
        hFB' (Finset.mem_union_right _ (hq1F ▸ mem_badMates hq1P hm1 h))
      have hB2 : (trackMate X q2).1 ∉ Bad := fun h =>
        hFB' (Finset.mem_union_right _ (hq2F ▸ mem_badMates hq2P hm2 h))
      have hdeg : (trackGraph X Lc G mk).deg q1.1 = 3 := by
        rw [hq1F]; exact (Finset.mem_filter.1 hFJ).2.1
      obtain ⟨d, hd, hdc, hap⟩ := hwit hfm X hX htri Lc (lam * D) t0 ρ cρ θ εc μ0 r0 G mk lab Ucl
        Bad Fl hW hr1 hμ1 q1 hq1P q2 hq2P (hq1F.trans hq2F.symm) hne hdeg (hq1F ▸ hFl)
        (hq1F ▸ hFB) hm1 hm2 hH1H hH2H hH1l hH2l hB1 hB2
      rw [hq1F] at hap
      exact ⟨d, hd, hdc, hap⟩)
  rw [Finset.card_image_of_injOn hinj] at hA
  have hB1 : (Bad.card : ℝ) ≤ |Mb| := hBad.trans (le_abs_self Mb)
  have h2 := hDbig X hX
  rw [div_le_iff₀ hε] at h2
  have hE : ((Dset.filter (fun F => F ∈ Bad')).card : ℝ) ≤ 5 * Bad.card := by
    exact_mod_cast hExc.trans hBad'card
  show 4 * ((trackGraph X Lc G mk).defJ G.good Fl : ℝ) ≤ ε * D
  have hdef : (trackGraph X Lc G mk).defJ G.good Fl = Dset.card := rfl
  rw [hdef, ← hsplit, Nat.cast_add]
  linarith

set_option maxHeartbeats 1000000 in
/-- **§13.3, the algebraic exclusion step with the margin as hypothesis**: the exceptional `J–J`
edges (neither end can receive them) are few. -/
theorem excE_count {ε lam θ : ℝ} (hε : 0 < ε) (hlam : 0 < lam) (hθ : 0 < θ) :
    ∃ ρ, 0 < ρ ∧ ∃ tol, 0 < tol ∧ ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, IsRoundCentre ρ X O →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → NoIntermediatePorts X (a * diam X) (lam * diam X) G →
          ∀ Fl : Finset (Set ℂ), HasUnflaggedMargin X (a * diam X) θ tol G mk Fl →
          qExcE X (a * diam X) G mk Fl ≤ ε * diam X := by
  obtain ⟨Nc, hclus⟩ := long_sides_clustered hlam
  obtain ⟨r0, hr0, μ0, hμ0, hfew⟩ := directions_few_of_exact 2 (fun _ => true)
    (isCompact_jjAdm 6 (θ / 2)) (capDegK 2) (fun d hd => jj_exact_card_le 6 (half_pos hθ) hd)
    (zeroNcent Nc) (ε := ε / 8) (by positivity)
  set ρ : ℝ := min (θ / 2) (r0 / 8) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρθ : ρ ≤ θ / 2 := min_le_left _ _
  have hρr : ρ ≤ r0 / 8 := min_le_right _ _
  obtain ⟨cρ, hcρ, hclose⟩ := labDir_close hρ
  set εc : ℝ := μ0 / 7 with hεcdef
  have hεc : 0 < εc := by positivity
  obtain ⟨Mb, hclusM⟩ := hclus εc hεc
  set t0 : ℝ := min ρ (cρ / 8) with ht0def
  have ht0 : 0 < t0 := lt_min hρ (by positivity)
  have ht0ρ : t0 ≤ ρ := min_le_left _ _
  have ht0c : t0 ≤ cρ / 8 := min_le_right _ _
  refine ⟨1, one_pos, t0, ht0, cρ / 8, by positivity, fun a ha hab => ?_⟩
  filter_upwards [hfew, hclose, hclusM, jj_witness, card_trackEnds,
    eventually_diam_ge (240 * |Mb| / ε), eventually_diam_ge (16 / cρ), eventually_diam_ge 1] with
    n hfewn hclosen hclusn hwit hends hDbig hDbig2 hD1
  intro hfm X hX htri O _ G mk hmk hwin hnoint Fl hmarg
  have hD : 0 < diam X := lt_of_lt_of_le one_pos (hD1 X hX)
  set D := diam X with hDdef
  set Lc := a * D with hLc
  obtain ⟨lab, hlab, hmarF⟩ := hmarg.labelledBy hX.1.2
  obtain ⟨Ucl, hUcl, Bad, hBad, hcl⟩ := hclusn hfm X hX htri
  have hends' := hends hfm X hX htri
  have hpar : 2 * (2 * t0 * D + 1 + Lc) ≤ cρ * D := by
    have h1 : 16 ≤ cρ * D := by
      have := hDbig2 X hX; rw [div_le_iff₀ hcρ] at this; linarith
    have h2 : t0 * D ≤ cρ / 8 * D := mul_le_mul_of_nonneg_right ht0c hD.le
    have h3 : a * D ≤ cρ / 8 * D := mul_le_mul_of_nonneg_right hab hD.le
    nlinarith
  have hW : WitnessCtx X Lc (lam * D) t0 ρ cρ θ εc G mk lab Ucl Bad Fl :=
    ⟨hmk, hnoint, hlab, hcl, hclosen X hX, hmarF, hθ, hρθ, hpar, hεc.le, ht0.le, by positivity⟩
  have hr1 : 2 * t0 + 4 * ρ < r0 := by linarith
  have hμ1 : 6 * εc < μ0 := by rw [hεcdef]; linarith
  set g := trackGraph X Lc G mk with hg
  -- the exceptional half-edges and their faces
  set S := (unmarkedPorts X Lc G mk).filter (fun q => TrackMated X Lc G mk q ∧
    (q.1 ∈ g.Js G.good ∧ (trackMate X q).1 ∈ g.Js G.good ∧ ¬ g.Qual G.good Fl q.1 ∧
      ¬ g.Qual G.good Fl (trackMate X q).1)) with hS
  have hE1 : g.excE G.good Fl ≤ S.card := by
    unfold LocalCharge.StubGraph.excE
    rw [hS]
    convert LocalCharge.StubGraph.card_E_filter_le (P := unmarkedPorts X Lc G mk) (v := Prod.fst)
      (mate := trackMate X) (mated := TrackMated X Lc G mk)
      (fun x y => x ∈ g.Js G.good ∧ y ∈ g.Js G.good ∧ ¬ g.Qual G.good Fl x ∧
        ¬ g.Qual G.good Fl y)
  have hE2 : S.card ≤ 3 * (S.image Prod.fst).card :=
    card_le_three_mul_image hends' (Finset.filter_subset _ _) fun q hq =>
      (Finset.mem_filter.1 (Finset.mem_filter.1 hq).2.2.1).2.1
  set Fs := S.image Prod.fst with hFs
  set Bad1 := Bad ∪ badMates X Lc G mk Bad with hBad1
  set Bad2 := Bad1 ∪ badMates X Lc G mk Bad1 with hBad2
  have hBad1card : Bad1.card ≤ 5 * Bad.card := by
    show (Bad ∪ badMates X Lc G mk Bad).card ≤ 5 * Bad.card
    have := card_badMates_le hends' hmk hwin Bad
    have := Finset.card_union_le Bad (badMates X Lc G mk Bad)
    omega
  have hBad2card : Bad2.card ≤ 5 * Bad1.card := by
    show (Bad1 ∪ badMates X Lc G mk Bad1).card ≤ 5 * Bad1.card
    have := card_badMates_le hends' hmk hwin Bad1
    have := Finset.card_union_le Bad1 (badMates X Lc G mk Bad1)
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := Fs) (fun F => F ∈ Bad2)
  have hExc : (Fs.filter (fun F => F ∈ Bad2)).card ≤ Bad2.card :=
    Finset.card_le_card fun F hF => (Finset.mem_filter.1 hF).2
  set Rest := Fs.filter (fun F => F ∉ Bad2) with hRest
  have hRestgood : Rest ⊆ G.good := by
    intro F hF
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hF).1
    exact (mem_unmarkedPorts.1 (Finset.mem_filter.1 hq).1).1
  have hinj : Set.InjOn lab Rest := hlab.1.mono hRestgood
  -- an unflagged `J` face that cannot receive has an unflagged `H` neighbour
  have hHn : ∀ F, ¬ g.Qual G.good Fl F → F ∉ Fl ∧ ∃ q1 ∈ unmarkedPorts X Lc G mk, q1.1 = F ∧
      TrackMated X Lc G mk q1 ∧ (trackMate X q1).1 ∈ g.Hs G.good ∧ (trackMate X q1).1 ∉ Fl := by
    intro F hF
    simp only [LocalCharge.StubGraph.Qual, not_or] at hF
    refine ⟨hF.1, ?_⟩
    have hc := (Nat.pos_of_ne_zero hF.2).trans_le (trackGraph_inc_le hends' F _)
    obtain ⟨q1, hq1⟩ := Finset.card_pos.1 hc
    obtain ⟨hq1P, hq1F, hm1, hH1⟩ := Finset.mem_filter.1 hq1
    exact ⟨q1, hq1P, hq1F, hm1, (Finset.mem_sdiff.1 hH1).1, (Finset.mem_sdiff.1 hH1).2⟩
  have hA := hfewn X hX (zeroCentres Ucl) (card_zeroCentres_le hUcl) (Rest.image lab)
    (fun p hp => by
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 (hlab.2 F (hRestgood hF)).1).1)
    (fun p hp => by
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hFs, hFB2⟩ := Finset.mem_filter.1 hF
      obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.1 hFs
      obtain ⟨hqP, hm, hJ1, hJ2, hQ1, hQ2⟩ := Finset.mem_filter.1 hqS
      obtain ⟨hF1l, q1, hq1P, hq1F, hm1, hH1, hH1l⟩ := hHn _ hQ1
      obtain ⟨hF2l, q2, hq2P, hq2F, hm2, hH2, hH2l⟩ := hHn _ hQ2
      have hF1B : q.1 ∉ Bad := fun h => hFB2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hF2B : (trackMate X q).1 ∉ Bad := fun h =>
        hFB2 (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_badMates hqP hm h)))
      have hB1 : (trackMate X q1).1 ∉ Bad := fun h =>
        hFB2 (Finset.mem_union_left _ (Finset.mem_union_right _ (hq1F ▸ mem_badMates hq1P hm1 h)))
      have hB2 : (trackMate X q2).1 ∉ Bad := by
        intro h
        have h1 : (trackMate X q).1 ∈ Bad1 :=
          Finset.mem_union_right _ (hq2F ▸ mem_badMates hq2P hm2 h)
        exact hFB2 (Finset.mem_union_right _ (mem_badMates hqP hm h1))
      exact hwit hfm X hX htri Lc (lam * D) t0 ρ cρ θ εc μ0 r0 G mk lab Ucl Bad Fl hW hr1 hμ1 q hqP
        hm hJ1 hJ2 hF1l hF2l hF1B hF2B q1 hq1P hq1F hm1 hH1 hH1l hB1 q2 hq2P hq2F hm2 hH2 hH2l hB2)
  rw [Finset.card_image_of_injOn hinj] at hA
  have hB1 : (Bad.card : ℝ) ≤ |Mb| := hBad.trans (le_abs_self Mb)
  have h2 := hDbig X hX
  rw [div_le_iff₀ hε] at h2
  have hE : ((Fs.filter (fun F => F ∈ Bad2)).card : ℝ) ≤ 25 * Bad.card := by
    exact_mod_cast hExc.trans (hBad2card.trans (by omega))
  have hcount : (g.excE G.good Fl : ℝ) ≤ 3 * (Fs.card : ℝ) := by exact_mod_cast hE1.trans hE2
  show (g.excE G.good Fl : ℝ) ≤ ε * D
  rw [← hsplit, Nat.cast_add] at hcount
  linarith

end Erdos99
end

end FlaggedCount

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FlaggedExclusion`
-/

section FlaggedExclusion

/-!
# The flagged local exclusion estimates (Verification Guide §§13.2–13.3)

The estimates `defective_J_few` (§13.2) and `exceptional_JJ_few` (§13.3) use the margin of the
unflagged faces.  The flags are detected in a band of width `δ D` about the circle of radius `D/2`
about the centre `O`, so `O` must be the centre supplied by **two-sided roundness**
(`IsRoundCentre`), not merely the centre of an enclosing disc: on the far side of the hull a
one-sided centre may leave the ports outside the band.  The statement form is therefore
`RoundLocalExclusion`: as `LocalExclusion`, but with a roundness defect `ρ` chosen after
`ε, λ, θ, δ` (so that `√(3ρ) + tol ≤ δ / 2`, and the diameter is large) and with `O` a centre of
two-sided roundness with defect at most `ρ`.

Each estimate is split into
* the **geometric margin step** (proved, `UnflaggedMargin`): every retained port of a good
  face satisfies the radial-band predicate, and for an unflagged good face it then satisfies
  `z · τ < -θ` (`saturated_unflagged_margin`); and
* the **algebraic exclusion step**, `defective_J_core` and `exceptional_JJ_core` (proved, from
  `FlaggedPoly`, `FlaggedPinning`, `FlaggedGeometry`, `FlaggedCount`): the
  statement `MarginExclusion Q`, in which the margin is a hypothesis (`HasUnflaggedMargin`) for an
  arbitrary set of flagged faces.

`defective_J_few` and `exceptional_JJ_few` are proved from these two steps.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- **A local exclusion estimate with a round centre** (the form of §§13.2–13.3): for every
`ε, λ, θ, δ > 0` there are a roundness defect `ρ > 0`, a saturation tolerance `tol > 0` and a
cutoff fraction `a₀ > 0` such that for every cutoff fraction `0 < a ≤ a₀`, eventually, for every
admissible configuration, every centre `O` of two-sided roundness with defect at most `ρ` and all
saturated good faces with a marking and the degree window at the cutoff `a D`, the quantity `Q`
evaluated with the flagged faces for `λ, θ, δ` is at most `ε D`. -/
def RoundLocalExclusion (Q : ChargeQuantity) : Prop :=
  ∀ ε, 0 < ε → ∀ lam, 0 < lam → ∀ θ δ : ℝ, 0 < θ → 0 < δ →
    ∃ ρ, 0 < ρ ∧ ∃ tol, 0 < tol ∧ ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, IsRoundCentre ρ X O →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → IsSaturated X (a * diam X) (lam * diam X) tol G mk →
          Q X (a * diam X) G mk (flaggedFaces X O (a * diam X) lam θ δ G) ≤ ε * diam X

/-- **The algebraic exclusion step with the margin as hypothesis**: for every `ε, λ, θ > 0` there
are `ρ, tol, a₀ > 0` such that for every `0 < a ≤ a₀`, eventually, for every admissible
configuration with a centre of two-sided roundness of defect at most `ρ`, all good faces with a
marking, the degree window and no intermediate ports at the cutoff `a D`, and every set `Fl` of
flagged faces such that the source labels (tolerance `tol`) have the unflagged margin `θ` outside
`Fl`, the quantity `Q` is at most `ε D`. -/
def MarginExclusion (Q : ChargeQuantity) : Prop :=
  ∀ ε, 0 < ε → ∀ lam, 0 < lam → ∀ θ, 0 < θ →
    ∃ ρ, 0 < ρ ∧ ∃ tol, 0 < tol ∧ ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, IsRoundCentre ρ X O →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → NoIntermediatePorts X (a * diam X) (lam * diam X) G →
          ∀ Fl : Finset (Set ℂ), HasUnflaggedMargin X (a * diam X) θ tol G mk Fl →
          Q X (a * diam X) G mk Fl ≤ ε * diam X

/-- **From the margin to the flags.**  An algebraic exclusion estimate with the margin as hypothesis
gives the local exclusion estimate with a round centre: the margin is supplied by
`saturated_unflagged_margin`, choosing `ρ` and `tol` with `√(3ρ) + tol ≤ δ / 2` and using
`D ≥ 1 / δ` eventually. -/
theorem roundLocalExclusion_of_margin {Q : ChargeQuantity} (h : MarginExclusion Q) :
    RoundLocalExclusion Q := by
  intro ε hε lam hlam θ δ hθ hδ
  obtain ⟨ρ₁, hρ₁, tol₁, htol₁, a₀, ha₀, hcore⟩ := h ε hε lam hlam θ hθ
  set ρ := min ρ₁ (δ ^ 2 / 48) with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ (by positivity)
  set tol := min tol₁ (δ / 4) with htoldef
  have htol : 0 < tol := lt_min htol₁ (by positivity)
  refine ⟨ρ, hρ, tol, htol, a₀, ha₀, fun a ha hab => ?_⟩
  filter_upwards [hcore a ha hab, saturated_unflagged_margin,
    tendsto_minDiam.eventually_ge_atTop (1 / δ), eventually_ge_atTop 2] with
    n hc hmar hDbig hn2 hfm X hX htri O hO G mk hmk hwin hsat
  have hD : 0 < diam X := hX.diam_pos hn2
  rw [← hX.diam_eq] at hDbig
  obtain ⟨ηr, δr, hR, hδr⟩ := hO
  have hδr0 : 0 ≤ δr := hR.η_nonneg.trans hR.η_le
  -- the radial band lies inside the flag band
  have hsq : √(3 * δr) ≤ δ / 4 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : δr ≤ δ ^ 2 / 48 := hδr.trans (min_le_right _ _)
    nlinarith
  have hsmall : √(3 * δr) + tol ≤ δ / 2 := by
    have : tol ≤ δ / 4 := min_le_right _ _
    linarith
  have hDδ : 1 ≤ δ * diam X := by
    rw [div_le_iff₀ hδ] at hDbig; linarith
  have hband := radial_band_le_flag hsmall hDδ hD.le
  have hM := hmar hfm X hX htri O ηr δr hR (a * diam X) lam θ δ tol G mk (by positivity) hsat hband
  exact hc hfm X hX htri O ⟨ηr, δr, hR, hδr.trans (min_le_left _ _)⟩ G mk hmk hwin hsat.1 _
    (hM.mono_tol (min_le_left _ _) hD.le)

/-- **Two unflagged `H` neighbours at an unflagged `J` are pinned, algebraic step** (Verification
Guide §13.2; proved via `defJ_count`).  With the unflagged margin as hypothesis: the unit condition `a a* = 1` at
the remaining port of an unflagged `J` with two unflagged `H` responses `z₁, z₂` fails
identically, since `a / T → A` with `Re A > 0` and the constant `B` of `a*` is `conj v` plus
conjugate retained-pair sums whose constituents have projection `≤ -θ` on the common tangent. -/
theorem defective_J_core : MarginExclusion qDefJ :=
  fun _ hε _ hlam _ hθ => defJ_count hε hlam hθ

/-- **Adjacent unflagged `J` faces with unflagged `H` neighbours are pinned, algebraic step**
(Verification Guide §13.3; proved via `excE_count`).  With the unflagged margin as hypothesis: identity (H1) for
`aᵢ = lᵢ ζ + vᵢ + zᵢ` has nonzero cubic coefficient `A₁ A₂ (A₁ + A₂) B₁ B₂ (B₁ + B₂)`. -/
theorem exceptional_JJ_core : MarginExclusion qExcE :=
  fun _ hε _ hlam _ hθ => excE_count hε hlam hθ

/-- **Two unflagged `H` neighbours at an unflagged `J` are pinned** (Verification Guide §13.2), with
the centre of two-sided roundness.  Proved from the margin step and the algebraic step
`defective_J_core`. -/
theorem defective_J_few : RoundLocalExclusion qDefJ :=
  roundLocalExclusion_of_margin defective_J_core

/-- **Adjacent unflagged `J` faces with unflagged `H` neighbours are pinned** (Verification Guide
§13.3), with the centre of two-sided roundness.  Proved from the margin step and the algebraic
step `exceptional_JJ_core`. -/
theorem exceptional_JJ_few : RoundLocalExclusion qExcE :=
  roundLocalExclusion_of_margin exceptional_JJ_core

end Erdos99

end

end FlaggedExclusion

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ChargingCutoff`
-/

section ChargingCutoff

/-!
# The cutoff choice for the charging argument (Verification Guide §11)

This file proves `charging_graph_exists` (the geometric input of the charging argument) from the
residual statement `charging_tracks_residual`, through the following chain (each arrow proved):

  [`saturation_core`, five local exclusion estimates] (proved, `ChargingResidual`)
    → `charging_tracks_residual` → `charging_tracks_local` → `charging_graph_local`
    → `charging_graph_exists`.

* `ChargingData X O ε η M L`: the conclusion of `charging_graph_exists` for a given cutoff `L`
  (good faces with small error budgets and a charging graph with flagged ports, the cap bounds
  (C7) and few pinned patterns).
* `TrackChargingData`: the same for the charging graph of the actual short tracks (`trackGraph`,
  `TrackChargingGraph`), given good faces with a marking (`IsMarking`) and the degree window
  (`DegreeWindow`).  `chargingData_of_track`: this graph is a `ChargingGraph`, because every track
  has exactly two ends.
* `TrackResidualData`: the same with the cap bounds (C7) replaced by the residual statement that
  few stubs end at unit hull sides or at marked ports, few stubs at degree-two faces end at
  `C₁` caps, and there are few `H–H` edges.  `trackChargingData_of_residual`: the remaining
  contributions to (C7) are bounded by `2 c₂ - C₁` (resp. `2 (c₂ - C₁)`), `3 ρ` and `Bface`
  (`TrackCapBounds`), and `ρ` is small by stability.
* `charging_tracks_residual` (proved from the components in `ChargingResidual`: saturation
  `saturation_exists` (proved), and the five local exclusion estimates: `hh_edges_few`,
  `oneShort_H_stubs_few` and `capless_small_few` are proved; `defective_J_few` and
  `exceptional_JJ_few` (`FlaggedExclusion`, stated with a centre of two-sided roundness) are
  proved from the unflagged margin and the (proved) algebraic steps `defective_J_core`,
  `exceptional_JJ_core`),
  `charging_tracks_local`, `charging_graph_local`: there is a
  shell density `κ > 0` such that for every macroscopic fraction `λ > 0` there is a smaller cutoff
  fraction `0 < a < λ` with the following property: eventually, whenever at most `κ D` tracks have
  length in `[a D, λ D)`, the respective data exist for the cutoff `L = a D`.  This is the content
  of §§10, 12, 13 and §11.2–§11.3 (saturation, uniform direction pinning, the local exclusion
  calculations, the choice of `a_{i+1}` after `a_i`, and the accounting of the intermediate faces)
  for one fixed index.
* `charging_graph_exists` (proved from `charging_graph_local`): the recursive choice of the
  thresholds `a₀ = ε > a₁ > a₂ > ⋯` (§11.2), followed by the finite pigeonhole argument of §11.1
  (`exists_sparse_track_shell`) to find a sparse shell `[a_{i+1} D, a_i D)`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The conclusion of `charging_graph_exists` for a fixed cutoff `L`: good faces `G` with small error
budgets and a charging graph whose flagged faces have flagged ports, satisfying the cap bounds (C7)
and with few pinned patterns. -/
def ChargingData (X : Finset Plane) (O : Plane) (ε η : ℝ) (M : ℕ) (L : ℝ) : Prop :=
  ∃ G : GoodFaces X,
    (G.Bface : ℝ) ≤ ε * diam X ∧ (unitReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
    (twoReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
    ∃ cg : ChargingGraph X L G,
      (∃ lam θ δ : ℝ, 0 < lam ∧ θ ≤ η ∧ δ ≤ η ∧ θ < aStar * lam / 4 ∧ δ < aStar * lam / 8 ∧
        ∀ F ∈ cg.flagged, ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T) ∧
      cg.capInc ≤ 2 * hullReturns X 2 - twoReturnsOneShort X L + ε * diam X ∧
      cg.hCapInc ≤ 2 * ((hullReturns X 2 : ℝ) - twoReturnsOneShort X L) + ε * diam X ∧
      cg.pinned M ≤ ε * diam X

/-- The conclusion of `charging_graph_local` for the charging graph of the actual short tracks
(`trackGraph`, §4.1): good faces `G` with a marking `mk` (`marks F` marked short ports at each good
face, and between two and four unmarked short ports), small error budgets, and a set `Fl` of faces
with flagged ports, such that the track graph satisfies the cap bounds (C7) and has few pinned
patterns. -/
def TrackChargingData (X : Finset Plane) (O : Plane) (ε η : ℝ) (M : ℕ) (L : ℝ) : Prop :=
  ∃ G : GoodFaces X, ∃ mk : Set ℂ → Finset (Sym2 Plane), IsMarking X L G mk ∧ DegreeWindow X L G ∧
    (G.Bface : ℝ) ≤ ε * diam X ∧ (unitReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
    (twoReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
    ∃ Fl : Finset (Set ℂ),
      (∃ lam θ δ : ℝ, 0 < lam ∧ θ ≤ η ∧ δ ≤ η ∧ θ < aStar * lam / 4 ∧ δ < aStar * lam / 8 ∧
        ∀ F ∈ Fl, ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T) ∧
      ((trackGraph X L G mk).bIn G.good +
          2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
            ((trackGraph X L G mk).Hs G.good) : ℝ) ≤
        2 * hullReturns X 2 - twoReturnsOneShort X L + ε * diam X ∧
      ((trackGraph X L G mk).bIn ((trackGraph X L G mk).Hs G.good) +
          2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
            ((trackGraph X L G mk).Hs G.good) : ℝ) ≤
        2 * ((hullReturns X 2 : ℝ) - twoReturnsOneShort X L) + ε * diam X ∧
      ((trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Gs G.good) M +
          (trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Ks G.good) M +
          4 * (trackGraph X L G mk).defJ G.good Fl + (trackGraph X L G mk).excE G.good Fl : ℝ) ≤
        ε * diam X

/-- The residual data of the charging argument for the track graph: as `TrackChargingData`, but
with the cap bounds (C7) replaced by the statement that few stubs of the track graph end at unit
hull sides or at marked ports of good faces, few stubs at degree-two faces end at two-edge returns
with exactly one short port (`C₁` caps, §13.5), and there are few `H–H` edges (§13.1).  The
remaining contributions to (C7) are bounded in `TrackCapBounds`. -/
def TrackResidualData (X : Finset Plane) (O : Plane) (ε η : ℝ) (M : ℕ) (L : ℝ) : Prop :=
  ∃ G : GoodFaces X, ∃ mk : Set ℂ → Finset (Sym2 Plane), IsMarking X L G mk ∧ DegreeWindow X L G ∧
    (G.Bface : ℝ) ≤ ε * diam X ∧ (unitReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
    (twoReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
    ∃ Fl : Finset (Set ℂ),
      (∃ lam θ δ : ℝ, 0 < lam ∧ θ ≤ η ∧ δ ≤ η ∧ θ < aStar * lam / 4 ∧ δ < aStar * lam / 8 ∧
        ∀ F ∈ Fl, ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T) ∧
      ((stubsTo X L G mk G.good (UnitEnd X)).card + (stubsTo X L G mk G.good (MarkedEnd G mk)).card +
          (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (OneShortEnd X L)).card +
          2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
            ((trackGraph X L G mk).Hs G.good) : ℝ) ≤ ε * diam X ∧
      ((trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Gs G.good) M +
          (trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Ks G.good) M +
          4 * (trackGraph X L G mk).defJ G.good Fl + (trackGraph X L G mk).excE G.good Fl : ℝ) ≤
        ε * diam X

/-- **The charging argument at one fixed scale, residual form** (Verification Guide §§10–13).  For
all `ε, η > 0` and every component-size bound `M` there is a shell density `κ > 0` such that, for
every macroscopic fraction `λ > 0`, there are a cutoff fraction `0 < a < λ` and a roundness defect
`ρ > 0` with: eventually, for every admissible configuration and every centre `O` of a disc of
radius `D/2 + η D` containing it which is also a centre of two-sided roundness with defect at most
`ρ` (`IsRoundCentre`), if at most `κ D` tracks have length in `[a D, λ D)` (the intermediate
tracks), then `TrackResidualData` holds for the cutoff `L = a D`.  The defect `ρ` is the least of
those required by `defective_J_few` and `exceptional_JJ_few` (whose flag band must contain the
radial band of the ports of the good faces).

`κ` must not depend on `λ`: it is fixed by the error ledger (§11.3: the at most `κ D` intermediate
tracks have at most `2 κ D` terminal faces and these account for at most `12 κ D` ports, which are
treated as virtual caps).  The fraction `a` is chosen after `λ`, so that the bounded patterns of
§13 with short edges (fewer than `a D` rhombi) vary below the pinning tolerances for macroscopic
threshold `λ` (§11.2).

The ingredients are: saturation (§10) for the good faces, the marking, the degree window and the
unit and marked stubs; the sparse shell (§11.3) for the error budgets; roundness and port selection
(§6) for the flagged ports; and uniform direction pinning (§12) with the local exclusion
calculations of §13 for the `C₁` stubs at `H` (§13.5), the `H–H` edges (§13.1) and the pinned
patterns (§13.2–§13.4).

Proof (assembly): `κ` comes from `saturation_exists` (for `ε / 2`); the flagged faces are the
maximal admissible set `flaggedFaces` with `θ = δ = min η (a* λ / 16)`; the saturation tolerance and
the cutoff fraction `a` are the minima of those given by the five local exclusion estimates (and
`a ≤ λ / 2`).  `κ` is also at most `ε / 16`, so that the intermediate-track term of
`oneShort_H_stubs_few` is paid for by the sparse shell.  The sorried ingredients are
the local exclusion estimates of `ChargingResidual` (`saturation_faces` is proved in
`Saturation`). -/
theorem charging_tracks_residual (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (M : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℝ, 0 < lam → ∃ a : ℝ, 0 < a ∧ a < lam ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
        ((longTracks X (a * diam X) \ longTracks X (lam * diam X)).card : ℝ) ≤ κ * diam X →
        TrackResidualData X O ε η M (a * diam X) := by
  obtain ⟨κs, hκs, hsat⟩ := saturation_exists (ε / 2) (by positivity)
  set κ := min κs (ε / 16) with hκdef
  have hκ : 0 < κ := lt_min hκs (by positivity)
  have hκs' : κ ≤ κs := min_le_left _ _
  have hκε : κ ≤ ε / 16 := min_le_right _ _
  refine ⟨κ, hκ, fun lam hlam => ?_⟩
  have hθ0 : 0 < min η (aStar * lam / 16) := lt_min hη (by have := aStar_pos; positivity)
  set θ := min η (aStar * lam / 16) with hθdef
  have hθ4 : θ < aStar * lam / 4 := by
    have h1 : θ ≤ aStar * lam / 16 := min_le_right _ _
    have h2 : 0 < aStar * lam := mul_pos aStar_pos hlam
    linarith
  have hθ8 : θ < aStar * lam / 8 := by
    have h1 : θ ≤ aStar * lam / 16 := min_le_right _ _
    have h2 : 0 < aStar * lam := mul_pos aStar_pos hlam
    linarith
  obtain ⟨t1, ht1, b1, hb1, h1⟩ := hh_edges_few η hη (ε / 4) (by positivity) lam hlam θ θ hθ0 hθ0
  obtain ⟨t2, ht2, b2, hb2, h2⟩ :=
    oneShort_H_stubs_few (ε := ε / 8) (by positivity) hlam
  obtain ⟨t3, ht3, b3, hb3, h3⟩ :=
    capless_small_few η hη M (ε / 3) (by positivity) lam hlam θ θ hθ0 hθ0
  obtain ⟨ρ4, hρ4, t4, ht4, b4, hb4, h4⟩ :=
    defective_J_few (ε / 3) (by positivity) lam hlam θ θ hθ0 hθ0
  obtain ⟨ρ5, hρ5, t5, ht5, b5, hb5, h5⟩ :=
    exceptional_JJ_few (ε / 3) (by positivity) lam hlam θ θ hθ0 hθ0
  set tol := min t1 (min t2 (min t3 (min t4 t5))) with htol
  have htol0 : 0 < tol := lt_min ht1 (lt_min ht2 (lt_min ht3 (lt_min ht4 ht5)))
  set a := min (lam / 2) (min b1 (min b2 (min b3 (min b4 b5)))) with ha
  have ha0 : 0 < a := lt_min (by positivity) (lt_min hb1 (lt_min hb2 (lt_min hb3 (lt_min hb4 hb5))))
  have hal : a ≤ lam / 2 := min_le_left _ _
  have hab1 : a ≤ b1 := (min_le_right _ _).trans (min_le_left _ _)
  have hab2 : a ≤ b2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hab3 : a ≤ b3 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hab4 : a ≤ b4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hab5 : a ≤ b5 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have htt1 : tol ≤ t1 := min_le_left _ _
  have htt2 : tol ≤ t2 := (min_le_right _ _).trans (min_le_left _ _)
  have htt3 : tol ≤ t3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htt4 : tol ≤ t4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have htt5 : tol ≤ t5 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨a, ha0, by linarith, min ρ4 ρ5, lt_min hρ4 hρ5, ?_⟩
  filter_upwards [hsat lam a tol ha0 htol0, h1 a ha0 hab1, h2 a ha0 hab2, h3 a ha0 hab3,
    h4 a ha0 hab4, h5 a ha0 hab5, eventually_ge_atTop 2] with
    n hs e1 e2 e3 e4 e5 hn2 hfm X hX htri O hO hround hsh
  have hD : 0 < diam X := hX.diam_pos hn2
  have hshs : ((longTracks X (a * diam X) \ longTracks X (lam * diam X)).card : ℝ) ≤
      κs * diam X := hsh.trans (mul_le_mul_of_nonneg_right hκs' hD.le)
  have hshε : ((longTracks X (a * diam X) \ longTracks X (lam * diam X)).card : ℝ) ≤
      ε / 16 * diam X := hsh.trans (mul_le_mul_of_nonneg_right hκε hD.le)
  obtain ⟨G, mk, hmk, hwin, hsatG, hBf, hBu, hBt, hst⟩ := hs hfm X hX htri hshs
  have q1 := e1 hfm X hX htri O hO G mk hmk hwin (hsatG.mono_tol htt1 hD.le)
  have q2 := e2 hfm X hX htri G mk hmk (hsatG.mono_tol htt2 hD.le)
  have q3 := e3 hfm X hX htri O hO G mk hmk hwin (hsatG.mono_tol htt3 hD.le)
  have q4 := e4 hfm X hX htri O (hround.mono (min_le_left _ _)) G mk hmk hwin
    (hsatG.mono_tol htt4 hD.le)
  have q5 := e5 hfm X hX htri O (hround.mono (min_le_right _ _)) G mk hmk hwin
    (hsatG.mono_tol htt5 hD.le)
  simp only [qHH, qCapless, qDefJ, qExcE] at q1 q3 q4 q5
  have hε2 : ε / 2 * diam X ≤ ε * diam X := by nlinarith
  refine ⟨G, mk, hmk, hwin, hBf.trans hε2, hBu.trans hε2, hBt.trans hε2,
    flaggedFaces X O (a * diam X) lam θ θ G, ⟨lam, θ, θ, hlam, min_le_left _ _, min_le_left _ _,
      hθ4, hθ8, fun F hF => mem_flaggedFaces hF⟩, by linarith, by linarith⟩

/-- The residual data give the track data: the cap bounds (C7) follow from the bounds of
`TrackCapBounds` (`trackGraph_capInc_le`, `trackGraph_hCapInc_le`) when `ρ` is small. -/
theorem trackChargingData_of_residual {X : Finset Plane} {O : Plane} {ε η : ℝ} {M : ℕ} {L : ℝ}
    (hX : IsSeparated X)
    (hdeg : ∀ p ∈ ccwHullSides X, portDeg X (Sum.inr p) = returnLength X p.1 p.2)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    (hρ : (returnExcess X : ℝ) ≤ ε / 5 * diam X) (h : TrackResidualData X O (ε / 5) η M L) :
    TrackChargingData X O ε η M L := by
  obtain ⟨G, mk, hmk, hwin, hBf, hBu, hBt, Fl, hfl, hres, hpin⟩ := h
  have hεD : ε / 5 * diam X ≤ ε * diam X := by nlinarith
  refine ⟨G, mk, hmk, hwin, hBf.trans hεD, hBu.trans hεD, hBt.trans hεD, Fl, hfl, ?_, ?_,
    hpin.trans hεD⟩
  · have h1 : ((trackGraph X L G mk).bIn G.good +
        2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
          ((trackGraph X L G mk).Hs G.good) + twoReturnsOneShort X L : ℝ) ≤
        2 * hullReturns X 2 + (stubsTo X L G mk G.good (UnitEnd X)).card +
          (stubsTo X L G mk G.good (MarkedEnd G mk)).card +
          2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
            ((trackGraph X L G mk).Hs G.good) + 3 * returnExcess X + G.Bface := by
      exact_mod_cast trackGraph_capInc_le hX hdeg hends
    have h0 : (0 : ℝ) ≤ (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (OneShortEnd X L)).card :=
      Nat.cast_nonneg _
    linarith
  · have h1 : ((trackGraph X L G mk).bIn ((trackGraph X L G mk).Hs G.good) +
        2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
          ((trackGraph X L G mk).Hs G.good) + 2 * twoReturnsOneShort X L : ℝ) ≤
        2 * hullReturns X 2 +
          (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (UnitEnd X)).card +
          (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (OneShortEnd X L)).card +
          (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (MarkedEnd G mk)).card +
          2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
            ((trackGraph X L G mk).Hs G.good) + 3 * returnExcess X + G.Bface := by
      exact_mod_cast trackGraph_hCapInc_le hX hdeg hends
    have hHsub : (trackGraph X L G mk).Hs G.good ⊆ G.good := Finset.filter_subset _ _
    have h2 : ((stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (UnitEnd X)).card : ℝ) ≤
        (stubsTo X L G mk G.good (UnitEnd X)).card := by
      exact_mod_cast Finset.card_le_card (stubsTo_mono hHsub _)
    have h3 : ((stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (MarkedEnd G mk)).card : ℝ) ≤
        (stubsTo X L G mk G.good (MarkedEnd G mk)).card := by
      exact_mod_cast Finset.card_le_card (stubsTo_mono hHsub _)
    linarith

/-- **The charging argument at one fixed scale, for the track graph** (Verification Guide
§§10–13).  The statement of `charging_tracks_residual` with the cap bounds (C7) for the track graph;
proved from `charging_tracks_residual`, the cap bounds of `TrackCapBounds` and
stability (`ρ = o(D)`, `stability_bounds`). -/
theorem charging_tracks_local (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (M : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℝ, 0 < lam → ∃ a : ℝ, 0 < a ∧ a < lam ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
        ((longTracks X (a * diam X) \ longTracks X (lam * diam X)).card : ℝ) ≤ κ * diam X →
        TrackChargingData X O ε η M (a * diam X) := by
  have hε5 : 0 < ε / 5 := by positivity
  obtain ⟨κ, hκ, h⟩ := charging_tracks_residual (ε / 5) η hε5 hη M
  refine ⟨κ, hκ, fun lam hlam => ?_⟩
  obtain ⟨a, ha0, hal, ρ, hρ, hev⟩ := h lam hlam
  refine ⟨a, ha0, hal, ρ, hρ, ?_⟩
  filter_upwards [hev, card_trackEnds, portDeg_hullSide, stability_bounds (ε / 5) hε5] with
    n hn hends hdeg hst hfm X hX htri O hO hround hsh
  exact trackChargingData_of_residual hX.1.2 (hdeg hfm X hX)
    (hends hfm X hX htri) (hst hfm X hX htri).2.1 (hn hfm X hX htri O hO hround hsh)

/-- The track data give a charging graph: `trackChargingGraph` is a `ChargingGraph` whenever every
track has exactly two ends. -/
theorem chargingData_of_track {X : Finset Plane} {O : Plane} {ε η : ℝ} {M : ℕ} {L : ℝ}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (h : TrackChargingData X O ε η M L) :
    ChargingData X O ε η M L := by
  obtain ⟨G, mk, hmk, hwin, hBf, hBu, hBt, Fl, hfl, hC, hHC, hpin⟩ := h
  exact ⟨G, hBf, hBu, hBt, trackChargingGraph hends hmk hwin Fl, hfl, hC, hHC, hpin⟩

/-- **The charging argument at one fixed scale** (Verification Guide §§10–13).  For all
`ε, η > 0` and every component-size bound `M` there is a shell density `κ > 0` such that, for every
macroscopic fraction `λ > 0`, there is a cutoff fraction `0 < a < λ` with: eventually, for every
admissible configuration and every centre `O` of a disc of radius `D/2 + η D` containing it, if at
most `κ D` tracks have length in `[a D, λ D)` (the intermediate tracks), then `ChargingData` holds
for the cutoff `L = a D`.  Proved from `charging_tracks_local` with the charging graph
of the short tracks (`trackChargingGraph`). -/
theorem charging_graph_local (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (M : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℝ, 0 < lam → ∃ a : ℝ, 0 < a ∧ a < lam ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
        ((longTracks X (a * diam X) \ longTracks X (lam * diam X)).card : ℝ) ≤ κ * diam X →
        ChargingData X O ε η M (a * diam X) := by
  obtain ⟨κ, hκ, h⟩ := charging_tracks_local ε η hε hη M
  refine ⟨κ, hκ, fun lam hlam => ?_⟩
  obtain ⟨a, ha0, hal, ρ, hρ, hev⟩ := h lam hlam
  refine ⟨a, ha0, hal, ρ, hρ, ?_⟩
  filter_upwards [hev, card_trackEnds] with n hn hends hfm X hX htri O hO hround hsh
  exact chargingData_of_track (hends hfm X hX htri) (hn hfm X hX htri O hO hround hsh)

/-- **The geometric input of the charging argument** (Verification Guide §§4.4, 6, 10–13; WP2,
WP5, WP8, WP10).  For every `ε, η > 0` and every component-size bound `M` there is a roundness
defect `ρ > 0` such that, eventually: for every centre `O` of a disc of radius `D/2 + η D`
containing the configuration which is also a centre of two-sided roundness with defect at most `ρ`
(`IsRoundCentre`; `ρ` is the least of the defects required at the finitely many thresholds
`a₀, …, a_{J-1}`), there are a cutoff
`0 < L ≤ ε D`, good faces `G` and a charging graph such that

* the exceptional faces outside `G` have at most `ε D` sides in total, and at most `ε D` unit and
  at most `ε D` two-edge hull returns have no short port;
* every flagged face has a flagged port (`IsFlaggedPort`) on a track with at least `L` rhombi, for a
  macroscopic fraction `λ > 0` and tolerances `θ, δ ≤ η` with `θ < a* λ / 4`, `δ < a* λ / 8`;
* the cap bounds (C7) hold: `C ≤ 2 c₂ - C₁ + ε D` and `hC ≤ 2 (c₂ - C₁) + ε D`;
* the pinned patterns of §13 (capless components with at most `M` faces in `G` or in `K`,
  defective `J` faces, exceptional `J–J` edges) number at most `ε D` in total (with weight four for
  the defective faces).

Proof (§11): the thresholds `a₀ = ε > a₁ > ⋯` are chosen recursively by `charging_graph_local`
(each `a_{i+1}` after `a_i`); with `J > Cs / κ` shells the finite pigeonhole argument
`exists_sparse_track_shell` gives an index `i < J` whose shell `[a_{i+1} D, a_i D)` contains at most
`κ D` tracks, and `charging_graph_local` for `λ = a_i` gives the data at the cutoff
`L = a_{i+1} D ≤ ε D`.  The ingredients of `charging_tracks_residual` are all proved. -/
theorem charging_graph_exists (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) (M : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
      ∃ L : ℝ, 0 < L ∧ L ≤ ε * diam X ∧ ∃ G : GoodFaces X,
        (G.Bface : ℝ) ≤ ε * diam X ∧ (unitReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
        (twoReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
        ∃ cg : ChargingGraph X L G,
          (∃ lam θ δ : ℝ, 0 < lam ∧ θ ≤ η ∧ δ ≤ η ∧ θ < aStar * lam / 4 ∧ δ < aStar * lam / 8 ∧
            ∀ F ∈ cg.flagged, ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T) ∧
          cg.capInc ≤ 2 * hullReturns X 2 - twoReturnsOneShort X L + ε * diam X ∧
          cg.hCapInc ≤ 2 * ((hullReturns X 2 : ℝ) - twoReturnsOneShort X L) + ε * diam X ∧
          cg.pinned M ≤ ε * diam X := by
  obtain ⟨κ, hκ, hloc⟩ := charging_graph_local ε η hε hη M
  choose! f hf0 hflt g hg0 hP using hloc
  -- the recursively chosen thresholds `a₀ = ε`, `a_{i+1} = f a_i`
  let a : ℕ → ℝ := fun i => Nat.rec ε (fun _ x => f x) i
  have ha0 : a 0 = ε := rfl
  have haS : ∀ i, a (i + 1) = f (a i) := fun _ => rfl
  have hpos : ∀ i, 0 < a i := by
    intro i
    induction i with
    | zero => exact hε
    | succ i ih => rw [haS]; exact hf0 _ ih
  have hanti : Antitone a := antitone_nat_of_succ_le fun i => by
    rw [haS]; exact (hflt _ (hpos i)).le
  obtain ⟨Cs, hCs⟩ := exists_sparse_track_shell
  obtain ⟨J, hJ⟩ := exists_nat_gt (Cs / κ)
  have hJ' : Cs < J * κ := by rwa [div_lt_iff₀ hκ] at hJ
  -- the roundness defect: the least of those required at the first `J` thresholds
  set S : Finset ℝ := insert 1 ((Finset.range J).image fun i => g (a i)) with hSdef
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  set ρ := S.min' hSne with hρdef
  have hρ0 : 0 < ρ := by
    have hmem := S.min'_mem hSne
    rw [← hρdef, hSdef, Finset.mem_insert, Finset.mem_image] at hmem
    rcases hmem with h | ⟨i, -, hi⟩
    · rw [h]; exact one_pos
    · rw [← hi]; exact hg0 _ (hpos i)
  have hρle : ∀ i ∈ Finset.range J, ρ ≤ g (a i) := fun i hi =>
    S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))
  refine ⟨ρ, hρ0, ?_⟩
  have hall : ∀ᶠ n in atTop, ∀ i ∈ Finset.range J, numOptimalClasses n < ⊤ → ∀ X,
      IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre (g (a i)) X O →
      ((longTracks X (a (i + 1) * diam X) \ longTracks X (a i * diam X)).card : ℝ) ≤
        κ * diam X → ChargingData X O ε η M (a (i + 1) * diam X) := by
    rw [Filter.eventually_all_finset]
    intro i _
    have := hP (a i) (hpos i)
    rw [← haS] at this
    exact this
  filter_upwards [hall, hCs κ hκ J hJ' a hanti, eventually_ge_atTop 2] with
    n hn hsh hn2 hfm X hX htri O hO hround
  have hD : 0 < diam X := hX.diam_pos hn2
  obtain ⟨i, hi, hsparse⟩ := hsh hfm X hX htri
  refine ⟨a (i + 1) * diam X, mul_pos (hpos (i + 1)) hD, ?_, ?_⟩
  · have : a (i + 1) ≤ a 0 := hanti (Nat.zero_le (i + 1))
    rw [ha0] at this
    exact mul_le_mul_of_nonneg_right this hD.le
  · exact hn i (Finset.mem_range.2 hi) hfm X hX htri O hO
      (hround.mono (hρle i (Finset.mem_range.2 hi))) hsparse

end Erdos99

end

end ChargingCutoff

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TrackCountAssembly`
-/

section TrackCountAssembly

/-!
# Assembly of the track count (Verification Guide §2.6 and §14; WP12)

`track_count_assembled` proves the statement of `Erdos99.track_count` from

* the exact counting identities of WP3 (`exact_counts`): `b = u + c₂ + v`, `2s = 2b - Δ + 4f`,
  `f = p + h + f_hi`, `σ = p + 2h + σ_hi`, `Δ = u - σ - ρ`, `R = s - E`, `v ≤ ρ`;
* the degree identity with its signed defect (`degree_defect`, (D1) and (E1));
* first-order locking, `Δ ≥ 0` (`lockingDefect_nonneg`, WP4);
* stability (`stability_bounds`, WP7): `ρ` and `Hinc = Σ_{k ≥ 7} k f_k` are `o(D)`;
* the perimeter bound `b ≤ π D` (`hullVertices_card_le_pi_mul_diam`);
* the charging count `charging_count` (WP2, WP5, WP8, WP10, WP11): a cutoff
  `0 < L ≤ ε D`, a choice of good faces and a set of selected tracks such that the incidences
  outside the good faces (`Bface`), the unit returns without short port (`Bunit`) and the
  two-edge returns without short port (`Btwo`) are `o(D)`, and the charging inequality (D5)
  `4f ≤ 5Y + 4P + 4c₂ - 3C₁ + o(D)` holds.  It is proved here from the combinatorial charging
  ledger (`LocalCharge`, `ChargingGraph.four_f_le`) and the geometric input
  `charging_graph_exists` (`ChargingCutoff`), which rests on the open lemma
  `charging_tracks_residual`.

Every quantity in `charging_count` is defined from `X`, the cutoff and the good faces (`GoodFaces.Y`,
`GoodFaces.Bface`, `twoReturnsOneShort`, …), so it is not a restatement of `track_count` with
unspecified numbers.  The remaining derivation is the linear arithmetic of §2.3–§2.6.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- `σ_hi + 2 f_hi ≤ Hinc` and `f_hi ≤ σ_hi`: for a face with `k ≥ 7` sides,
`(k - 4) + 2 ≤ k` and `1 ≤ k - 4`. -/
lemma highFace_bounds {X : Finset Plane} (hX : IsSeparated X) :
    (highFaceExcess X : ℝ) + 2 * numHighFaces X ≤ highIncidence X ∧
      (numHighFaces X : ℝ) ≤ highFaceExcess X := by
  have hfin := finite_exceptionalFaces hX
  have hE : exceptionalFinset X = hfin.toFinset := by rw [exceptionalFinset, dif_pos hfin]
  rw [highIncidence_eq_sum hfin, highFaceExcess, numHighFaces, hE, Finset.card_eq_sum_ones]
  constructor
  · have : ∑ F ∈ hfin.toFinset.filter (fun F => 7 ≤ faceSize X F), (faceSize X F - 4) +
        2 * ∑ F ∈ hfin.toFinset.filter (fun F => 7 ≤ faceSize X F), 1 ≤
        ∑ F ∈ hfin.toFinset.filter (fun F => 7 ≤ faceSize X F), faceSize X F := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun F hF => by have := (Finset.mem_filter.1 hF).2; omega
    exact_mod_cast this
  · have : ∑ F ∈ hfin.toFinset.filter (fun F => 7 ≤ faceSize X F), 1 ≤
        ∑ F ∈ hfin.toFinset.filter (fun F => 7 ≤ faceSize X F), (faceSize X F - 4) :=
      Finset.sum_le_sum fun F hF => by have := (Finset.mem_filter.1 hF).2; omega
    exact_mod_cast this

/-- `|good| ≤ π D`: the good faces are exceptional faces, and `f ≤ σ ≤ u ≤ b ≤ π D` by `Δ ≥ 0`. -/
lemma card_good_le_pi_mul_diam :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ G : GoodFaces X, (G.good.card : ℝ) ≤ π * diam X := by
  filter_upwards [exact_counts, lockingDefect_nonneg, eventually_ge_atTop 2] with
    n hex hloc hn hfm X hX htri G
  have hsep : IsSeparated X := hX.1.2
  obtain ⟨hb, -, hf, hσ, hΔ, -, -⟩ := hex hfm X hX htri 1 one_pos
  have hΔ0 : (0 : ℝ) ≤ lockingDefect X := by exact_mod_cast hloc hfm X hX htri
  obtain ⟨-, hhi2⟩ := highFace_bounds hsep (X := X)
  have h2 : 2 ≤ X.card := by rw [hX.1.1]; exact hn
  have hbD := hullVertices_card_le_pi_mul_diam hsep h2
  have hg : (G.good.card : ℝ) ≤ numExceptional X := by exact_mod_cast G.card_good_le hsep
  have h0 : (0 : ℝ) ≤ numHexagons X := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ numLongReturns X := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ hullReturns X 2 := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ returnExcess X := Nat.cast_nonneg _
  linarith

/-- **The charging count** (Verification Guide §4, §6, §10, §11, §13; WP2, WP5, WP8, WP10, WP11).
For every `ε, η > 0` there is a roundness defect `ρ > 0` such that, eventually: for every centre `O`
of a disc of radius `D/2 + η D` containing the configuration which is also a centre of two-sided
roundness with defect at most `ρ` (`IsRoundCentre`), there are a cutoff `0 < L ≤ ε D`, a choice `G` of good faces and a set `sel` of
selected tracks (each with at least `L` rhombi, each satisfying the selected-track geometry) such
that

* the exceptional faces outside `G` have at most `ε D` sides in total (`Bface`),
* at most `ε D` unit hull returns and at most `ε D` two-edge hull returns have no short port, and
* the charging inequality (D5) holds: `4f ≤ 5Y + 4P + 4c₂ - 3C₁ + ε D`, with `P = |sel|`,
  `Y = GoodFaces.Y`, `c₂` the two-edge returns and `C₁` those with exactly one short port.

Proved from the geometric input `charging_graph_exists` (resting on the open lemma
`charging_tracks_residual`) and the combinatorial charging
ledger `ChargingGraph.four_f_le` (proved): with `δ = ε / 8` and the component-size bound
`M = ⌈2π/δ⌉`, the large capless components contribute at most `2|good|/(M+1) ≤ δ D` (since
`|good| ≤ π D`), the selected tracks are the tracks of the flagged ports, distinct for distinct
flagged faces by `flaggedPort_face_unique` (§6.4), and the remaining errors are at most
`7 δ D`. -/
theorem charging_count (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
      ∃ L : ℝ, 0 < L ∧ L ≤ ε * diam X ∧ ∃ G : GoodFaces X, ∃ sel ⊆ longTracks X L,
        (∀ T ∈ sel, IsSelectedTrack O (diam X) η T) ∧
        (G.Bface : ℝ) ≤ ε * diam X ∧ (unitReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
        (twoReturnsNoShort X L : ℝ) ≤ ε * diam X ∧
        4 * (numExceptional X : ℝ) ≤ 5 * G.Y L + 4 * sel.card + 4 * hullReturns X 2 -
          3 * twoReturnsOneShort X L + ε * diam X := by
  set δ := ε / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  set M : ℕ := ⌈2 * π / δ⌉₊ with hM
  obtain ⟨ρ, hρ, hcgρ⟩ := charging_graph_exists δ η hδ0 hη M
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hcgρ, card_good_le_pi_mul_diam,
    flaggedPort_face_unique, eventually_ge_atTop 2] with n hcg hgood huniq hn hfm X hX htri O hO
    hround
  have hsep : IsSeparated X := hX.1.2
  have hD : 0 < diam X := hX.diam_pos hn
  obtain ⟨L, hL0, hLδ, G, hBf, hBu, hBt, cg, ⟨lam, θ, dl, hlam, hθη, hdlη, hθ, hdl, hflag⟩, hC,
    hHC, hpin⟩ := hcg hfm X hX htri O hO hround
  choose! φ hφmem hφP using hflag
  have hinj : Set.InjOn φ cg.flagged := fun F hF F' hF' h =>
    huniq hfm X hX htri O (diam X) lam θ dl F F' (φ F) hD hθ hdl
      (Finset.mem_filter.1 (hφmem F hF)).1 (hφP F hF) (h ▸ hφP F' hF')
  have hδε : δ * diam X ≤ ε * diam X := by rw [hδ]; nlinarith
  refine ⟨L, hL0, hLδ.trans hδε, G, cg.flagged.image φ, ?_, ?_, hBf.trans hδε, hBu.trans hδε,
    hBt.trans hδε, ?_⟩
  · intro T hT
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hT
    exact hφmem F hF
  · intro T hT
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨-, e, he, -, ν, nn, hν, hn, hm, hf, hside⟩ := hφP F hF
    exact BoundaryPort.isSelectedTrack_of_port hD.le hθη hdlη he hν hn hm hf hside
  have hFl : (cg.flagged.card : ℝ) ≤ (cg.flagged.image φ).card := by
    rw [Finset.card_image_of_injOn hinj]
  have hg := hgood hfm X hX htri G
  have hMb : 2 * π / δ ≤ M := Nat.le_ceil _
  have hπ : 2 * π ≤ δ * M := by rw [div_le_iff₀ hδ0] at hMb; linarith
  have hlarge : 2 * (G.good.card : ℝ) / (M + 1) ≤ δ * diam X := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hmain := cg.four_f_le hsep M
  have hδD : δ * diam X = ε * diam X / 8 := by rw [hδ]; ring
  linarith

/-- **The track count, assembled** (Verification Guide §2.6, §14).  This is exactly the statement
of `Erdos99.track_count`, derived from the exact counts, the degree identity, locking, stability,
the perimeter bound and the charging count `charging_count`. -/
theorem track_count_assembled (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
      ∃ L : ℝ, 0 ≤ L ∧ L ≤ ε * diam X ∧ ∃ sel ⊆ longTracks X L,
        (∀ T ∈ sel, IsSelectedTrack O (diam X) η T) ∧
        ((longTracks X L).card : ℝ) - sel.card ≤ 3 / 5 * (π * diam X - sel.card) + ε * diam X := by
  have hδ : 0 < ε / 100 := by positivity
  obtain ⟨ρ, hρ, hchρ⟩ := charging_count (ε / 100) η hδ hη
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hchρ, stability_bounds (ε / 100) hδ, exact_counts,
    degree_defect, lockingDefect_nonneg, eventually_ge_atTop 2] with
    n hch hst hex hdd hloc hn hfm X hX htri O hO hround
  have hsep : IsSeparated X := hX.1.2
  have hD : 0 < diam X := hX.diam_pos hn
  obtain ⟨L, hL0, hLε, G, sel, hsel, hselT, hBf, hBu, hBt, hD5⟩ := hch hfm X hX htri O hO hround
  refine ⟨L, hL0.le, by nlinarith, sel, hsel, hselT, ?_⟩
  obtain ⟨hb, hs, hf, hσ, hΔ, hR, hv⟩ := hex hfm X hX htri L hL0
  have hd := abs_le.1 (hdd hfm X hX htri L G)
  have hΔ0 : (0 : ℝ) ≤ lockingDefect X := by exact_mod_cast hloc hfm X hX htri
  obtain ⟨-, hρ, -, -, -, hHinc⟩ := hst hfm X hX htri
  obtain ⟨hhi1, hhi2⟩ := highFace_bounds hsep (X := X)
  have h2 : 2 ≤ X.card := by rw [hX.1.1]; exact hn
  have hbD := hullVertices_card_le_pi_mul_diam hsep h2
  have hC₁ : (twoReturnsOneShort X L : ℝ) ≤ hullReturns X 2 := by
    exact_mod_cast twoReturnsOneShort_le X L
  have hA : (0 : ℝ) ≤ G.A := Nat.cast_nonneg _
  have hE : (numShortTracks X L : ℝ) =
      ((allTracks X).filter (fun T => (trackLength X T : ℝ) < L)).card := rfl
  have h0 : (0 : ℝ) ≤ numHexagons X := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ numLongReturns X := Nat.cast_nonneg _
  rw [← hE] at hR
  linarith

end Erdos99

end

end TrackCountAssembly

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CountingWitnessReduction`
-/

section CountingWitnessReduction

/-!
# Theorem 1.1 from the counting data

Theorem 1.1 (`Erdos99.erdos99_finite_multiplicity`) follows from the lemma
`Erdos99.exists_countingWitness` (formerly open, now proved in `Erdos99.lean`): below it is re-derived with that lemma's statement taken as a
hypothesis.  (`first_order_locking`
is no longer open by itself: it is derived in `FirstOrderLocking` from the lifted fan theorem
`lifted_form_no_negative_plane`, which is proved: the facet-link step `polytope_facetLinks` and the lifted fan
`lifted_fan_exists` are proved.)
(`contactGraph_connected`, `exists_shore_geometry` and `hull_direction_spread` are proved.)
-/

@[expose] public noncomputable section

open scoped BigOperators Real
open Classical

open Filter

namespace Erdos99

/-- Theorem 1.1, with the lemma `exists_countingWitness` (§§3.4–6 of the manuscript)
taken as the hypothesis `hW`.  Everything else used here is proved. -/
theorem erdos99_finite_multiplicity_of_countingWitness
    (hW : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X → Nonempty (CountingWitness X ε)) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → HasUnitTriangle X := by
  obtain ⟨ε, hε, hfin⟩ := final_contradiction
  filter_upwards [rhombi_card_lower ε hε, hW ε hε, rhombi_inside_card_le,
    eventually_ge_atTop 2] with n h1 h2 h3 hn2
  intro hfm X hX
  by_contra htri
  obtain ⟨w⟩ := h2 hfm X hX htri
  have hq := h1 hfm X hX htri
  have hD := hX.diam_pos hn2
  have hin := h3 hfm X hX htri (w.long \ w.sel) (Finset.sdiff_subset.trans w.long_subset)
  have hcard : ((w.long \ w.sel).card : ℝ) = (w.long.card : ℝ) - w.sel.card := by
    rw [Finset.card_sdiff_of_subset w.sel_subset, Nat.cast_sub (Finset.card_le_card w.sel_subset)]
  rw [hcard] at hin
  set L := (rhombi X).filter (fun R => ∃ T ∈ tracks X, T ∉ w.long ∧ Crosses T R)
  set Q := (rhombi X).filter (fun R => ∃ T ∈ w.sel, Crosses T R)
  set I := (rhombi X).filter (fun R => ∀ T ∈ tracks X, Crosses T R → T ∈ w.long \ w.sel)
  have hsub : rhombi X ⊆ L ∪ Q ∪ I := by
    intro R hR
    by_cases hL : ∃ T ∈ tracks X, T ∉ w.long ∧ Crosses T R
    · simp [L, hR, hL]
    by_cases hQ : ∃ T ∈ w.sel, Crosses T R
    · simp [Q, hR, hQ]
    refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hR, fun T hT hc => ?_⟩)
    refine Finset.mem_sdiff.2 ⟨?_, fun hs => hQ ⟨T, hs, hc⟩⟩
    by_contra hl
    exact hL ⟨T, hT, hl, hc⟩
  have hsplit : ((rhombi X).card : ℝ) ≤ L.card + Q.card + I.card := by
    have := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast this
  have hR := (abs_le.1 w.abs_R_sub).2
  refine hfin (diam X) (rhombi X).card w.long.card w.sel.card Q.card w.f w.β w.c₂ w.C₁ w.A hD hq
    (by linarith) w.f_add_c₂_le w.two_fifths (by exact_mod_cast w.C₁_le_c₂) (by positivity)
    (by positivity) (by exact_mod_cast Finset.card_le_card w.sel_subset)
    w.annular_linear w.annular_quadratic ?_
  have := w.short_loss
  linarith

end Erdos99

end

end CountingWitnessReduction

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Final`
-/

section Final

/-!
# Theorem 1.1 with the assembled track count

`erdos99_finite_multiplicity_assembled` is Theorem 1.1 (`Erdos99.erdos99_finite_multiplicity`)
proved with `track_count` replaced by `track_count_assembled` (`TrackCountAssembly`).  Its
proof does not use `track_count` (which is itself now derived from `track_count_assembled`, in
`Erdos99.lean`)  The
formerly open ingredients were

* `charging_tracks_residual` (`ChargingCutoff`; §§4.4, 6.4, 10–13 of the Verification
  Guide), the one-scale geometric input of the charging argument for the graph of the actual short
  tracks.  `charging_graph_exists` is derived from it (the pigeonhole cutoff choice of §11, the
  track charging graph and the cap bounds (C7) up to residual stubs, all proved in
  `ChargingCutoff`, `TrackChargingGraph`, `TrackCapBounds`).  The charging count `charging_count`
  (`TrackCountAssembly`) is derived from it and the combinatorial charging ledger
  (`LocalCharge`: degree identities (C1)–(C4), the spanning-forest component estimate (C2),
  the charge bounds (C5), (C6)), all proved,
* the fan theorem for the lift, through locking and stability.  `lifted_form_no_negative_plane`
  (`StressSign`) is now derived (`LiftedFan`, `FanTheorem`) from the proved
  lifted fan `lifted_fan_exists` and the proved step `polytope_facetLinks` (the triangulated
  facet links and edge lengths of a polytope, `FacetLinksProof`; the facet decomposition `polytope_facetForms` is
  derived from it using the proved row identity and mixed-volume symmetry, and the volume-Hessian
  theorem `polytopeHessian_noNegativePlane`, Guide §7.3 (e), is derived from it by Hilbert's
  argument, the planar Minkowski inequality and the connectivity of the facet graph, all proved).
  The integration of the gradient jumps of the fan matrix (Guide §7.3 (b), `fan_gradient_exists`,
  `FanGradientExists`), the convexity step (c) (`FanConvexity`) and the approximation by
  polytopes, steps (d), (f) (`FanApprox`), are proved.

(The cap landing lemma `cap_landing`, formerly open, is proved in `CapLanding`.)
-/

@[expose] public noncomputable section

open scoped BigOperators Real
open Filter

namespace Erdos99

/-- **Theorem 1.1 (finite-multiplicity assertion)**, with the track count assembled from the exact
counts, the degree identity, locking, stability and the charging count. -/
theorem erdos99_finite_multiplicity_assembled :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → HasUnitTriangle X :=
  erdos99_finite_multiplicity_of_countingWitness
    (fun ε hε => exists_countingWitness_of_round track_count_assembled ε hε)

/-- **Erdős Problem 99 under finite multiplicity**, via `erdos99_finite_multiplicity_assembled`. -/
theorem erdos99_of_finite_multiplicity_assembled
    (h : ∀ᶠ n in atTop, numOptimalClasses n < ⊤) : Erdos99Conjecture := by
  filter_upwards [h, erdos99_finite_multiplicity_assembled, eventually_ge_atTop 2] with
    n hn hmain hn2
  intro X hX
  exact hmain hn X ((isErdosOptimal_iff_isOptimal hn2 X).1 hX)

end Erdos99

end

end Final
