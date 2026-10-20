module

public import SKBarriers2.Main.Conditional
public import SKBarriers2.Bridge.ScalarDataConstruction
public import SKBarriers2.Static.FloorResponseDischarge
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

noncomputable section
open scoped NNReal Topology ContDiff
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2

theorem ScalarData.cdf_pos {β : ℝ} (D : ScalarData β) {t : ℝ} (ht : 0 < t) :
    0 < cdf (D.μ : Measure ℝ) t := by
  obtain ⟨c, T, hc, hT, hlow⟩ := D.lin_lower
  have hm : 0 < min t T := lt_min ht hT
  exact (mul_pos hc hm).trans_le
    ((hlow (min t T) ⟨hm.le, min_le_right _ _⟩).trans
      ((cdf (D.μ : Measure ℝ)).mono (min_le_left _ _)))

theorem ScalarData.cdf_lipschitzOn {β : ℝ} (D : ScalarData β) {a b : ℝ}
    (ha : 0 < a) (hb : b < D.q) :
    ∃ K : ℝ≥0, LipschitzOnWith K (cdf (D.μ : Measure ℝ)) (Icc a b) := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) D.q :=
    fun _ hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  exact (D.smooth.mono hsub).exists_lipschitzOnWith (by simp)
    (convex_Icc a b) isCompact_Icc

theorem ScalarData.localWindowGeometry {β : ℝ} (D : ScalarData β) {l r : ℝ}
    (hl : 0 < l) (_hlr : l ≤ r) (hr : r < D.q) :
    LocalWindowGeometry (cdf (D.μ : Measure ℝ)) (Icc l r) := by
  let u : ℝ := (r + D.q) / 2
  have hru : r < u := by dsimp only [u]; linarith
  have huq : u < D.q := by dsimp only [u]; linarith
  obtain ⟨K, hK⟩ := D.cdf_lipschitzOn hl huq
  let m : ℝ := cdf (D.μ : Measure ℝ) l
  have hm : 0 < m := D.cdf_pos hl
  have hK1 : 0 < (K : ℝ) + 1 := by positivity
  let d₀ : ℝ := min (l / 4) (min ((1 - r) / 6) (min (u - r) (m / (K + 1))))
  have hd₀ : 0 < d₀ := lt_min (by positivity)
    (lt_min (by linarith [D.q_mem.2]) (lt_min (sub_pos.mpr hru) (div_pos hm hK1)))
  refine ⟨l / 2, d₀, half_pos hl, hd₀, ?_⟩
  intro x hx d hd hdd
  have hd1 : d ≤ l / 4 := hdd.trans (min_le_left _ _)
  have hd2 : d ≤ (1 - r) / 6 :=
    hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : d ≤ u - r := hdd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hd4 : d ≤ m / (K + 1) := hdd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hxd : x + d ∈ Icc l u := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxu : x ∈ Icc l u := ⟨hx.1, hx.2.trans hru.le⟩
  have hdist := hK.dist_le_mul (x + d) hxd x hxu
  rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left, abs_of_pos hd] at hdist
  have hinc : cdf (D.μ : Measure ℝ) (x + d) - cdf (D.μ : Measure ℝ) x ≤ K * d :=
    (le_abs_self _).trans hdist
  have hKd : (K : ℝ) * d ≤ m := by
    have h := (le_div_iff₀ hK1).mp hd4
    nlinarith
  have hmx : m ≤ cdf (D.μ : Measure ℝ) x := (cdf (D.μ : Measure ℝ)).mono hx.1
  exact ⟨by linarith [hx.1], by linarith [hx.2], by linarith⟩

def ScalarData.conditionalScalarData {β : ℝ} (D : ScalarData β) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r) (hr : r < D.q) : ConditionalScalarData β D.μ := by
  let H : ℝ := min (l / 2) ((D.q - r) / 2)
  have hH : 0 < H := lt_min (half_pos hl) (half_pos (sub_pos.mpr hr))
  have hleft : 0 < l - H := by
    have h := min_le_left (l / 2) ((D.q - r) / 2)
    dsimp only [H]
    linarith
  have hright : r + H < D.q := by
    have h := min_le_right (l / 2) ((D.q - r) / 2)
    dsimp only [H]
    linarith
  let K : ℝ≥0 := (D.cdf_lipschitzOn hleft hright).choose
  have hK : LipschitzOnWith K (cdf (D.μ : Measure ℝ)) (Icc (l - H) (r + H)) :=
    (D.cdf_lipschitzOn hleft hright).choose_spec
  exact {
    l := l, r := r, u := (r + D.q) / 2, H := H
    m := cdf (D.μ : Measure ℝ) l, K := K
    l_pos := hl, lr := hlr, ru := by linarith
    u_one := by linarith [D.q_mem.2]
    H_pos := hH, m_pos := D.cdf_pos hl
    mass_one := D.mass_one, minimizer := D.minimizer, unique := D.unique
    mass_lower := le_rfl, lipschitz := hK
    overlap_id := fun t ht => D.overlap_id t ⟨hl.le.trans ht.1, by linarith [ht.2]⟩ }

def CornerInputs (β : ℝ) (D : ScalarData β) : Prop :=
  ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ D.q ∧
    ∀ l r : ℝ, 0 < l → l ≤ r → r < l₀ →
      LocalCubicGap β (cdf (D.μ : Measure ℝ)) (Icc l r) ∧
      LocalBoundaryControl β (cdf (D.μ : Measure ℝ)) (Icc l r)

theorem cornerInputs_of_all_windows {β : ℝ} (D : ScalarData β)
    (h : ∀ l r : ℝ, 0 < l → l ≤ r → r < D.q →
      LocalCubicGap β (cdf (D.μ : Measure ℝ)) (Icc l r) ∧
      LocalBoundaryControl β (cdf (D.μ : Measure ℝ)) (Icc l r)) :
    CornerInputs β D := by
  exact ⟨D.q, D.q_mem.1, le_rfl, h⟩

theorem conditionalRateData_of_cornerInputs {β : ℝ} (hβ : 1 < β) (D : ScalarData β)
    (hmean : ∃ Cb, 0 < Cb ∧ MeanRate β (2/3) Cb)
    (hvar : ∃ Cv, 0 < Cv ∧ VarianceCap β (7/15) Cv)
    (hcorner : CornerInputs β D) : Nonempty (ConditionalRateData β (2/3)) := by
  obtain ⟨Cb, _hCb, hmean⟩ := hmean
  obtain ⟨Cv, _hCv, hvar⟩ := hvar
  apply exists_conditionalRateData hβ (by norm_num) (by norm_num)
    hmean hvar (by norm_num) D.μ D.unique
  intro qs hqs _hqs1 cuts
  obtain ⟨l₀, hl₀, hl₀q, hcorner⟩ := hcorner
  let t : ℝ := min l₀ (min cuts.b' (min (cuts.b ^ 2 / 2) qs))
  have ht : 0 < t := lt_min hl₀ (lt_min cuts.b'_pos
    (lt_min (div_pos (sq_pos_of_pos cuts.b_pos) (by norm_num)) hqs))
  let l : ℝ := t / 4
  let r : ℝ := t / 2
  have hl : 0 < l := by dsimp only [l]; positivity
  have hlr : l < r := by dsimp only [l, r]; linarith
  have hrt : r < t := by dsimp only [r]; linarith
  have hrl₀ : r < l₀ := hrt.trans_le (min_le_left _ _)
  have hrq : r < D.q := hrl₀.trans_le hl₀q
  let d : ConditionalScalarData β D.μ := D.conditionalScalarData hl hlr.le hrq
  obtain ⟨hcubic, hboundary⟩ := hcorner l r hl hlr.le hrl₀
  obtain ⟨E₀, hE₀, hEs⟩ := localFractionalGap_of_cubicGap_uniform'
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) (cdf (D.μ : Measure ℝ)).mono
    D.minimizer hcubic D.floorTrial (D.localWindowGeometry hl hlr.le hrq) hboundary
  obtain ⟨g₀, hg₀, hgs⟩ := hEs E₀ ⟨hE₀, le_rfl⟩
  obtain ⟨S₀, hS₀, hSs⟩ := hgs (g₀ / 2) ⟨half_pos hg₀, by linarith⟩
  refine ⟨d, hlr, ?_, ?_, ?_, S₀, E₀, g₀ / 2, hS₀, hE₀, half_pos hg₀, ?_⟩
  · exact (show l < t by dsimp only [l]; linarith).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  · exact (show l < t by dsimp only [l]; linarith).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  · exact (show l < t by dsimp only [l]; linarith).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  · intro R hR
    obtain ⟨θ, hθ⟩ := exists_rateExponents (by norm_num : (0 : ℝ) < 2/3)
      (by norm_num : (2/3 : ℝ) < 3/4)
    apply hSs S₀ ⟨hS₀, le_rfl⟩ (rateRho R (2/3)) (rate_scales_tendsto_zero hθ R).1
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact mul_pos hR (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)

theorem mainStatement_of_cornerInputs
    (hmean : ∀ β, 1 < β → ∃ Cb, 0 < Cb ∧ MeanRate β (2/3) Cb)
    (hvar : ∀ β, 1 < β → ∃ Cv, 0 < Cv ∧ VarianceCap β (7/15) Cv)
    (hcorner : ∀ β (hβ : 1 < β), CornerInputs β (scalarData β hβ)) :
    OAI.SK.Strengthened.MainStatement := by
  apply mainStatement_of_rate_data
  intro β hβ
  exact conditionalRateData_of_cornerInputs hβ (scalarData β hβ)
    (hmean β hβ) (hvar β hβ) (hcorner β hβ)

theorem subcriticalStatement_of_cornerInputs
    (hmean : ∀ β, 1 < β → ∃ Cb, 0 < Cb ∧ MeanRate β (2/3) Cb)
    (hvar : ∀ β, 1 < β → ∃ Cv, 0 < Cv ∧ VarianceCap β (7/15) Cv)
    (hcorner : ∀ β (hβ : 1 < β), CornerInputs β (scalarData β hβ)) :
    OAI.SK.Strengthened.SubcriticalStatement := by
  apply subcriticalStatement_of_rate_data
  intro β hβ
  exact conditionalRateData_of_cornerInputs hβ (scalarData β hβ)
    (hmean β hβ) (hvar β hβ) (hcorner β hβ)

end SKBarriers2
