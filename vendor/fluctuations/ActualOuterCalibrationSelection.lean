module

public import ActualMixedClockCDF
public import ScalarLowClockCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem exists_outer_good_point {a b : ℝ} {cost : ℝ → ℝ} (hab : a < b)
    (hint : IntervalIntegrable cost volume a b)
    (hbudget : (∫ u in a..b, cost u) < b-a) :
    ∃ u ∈ Ioo a b, cost u < 1 := by
  by_contra hn
  have hbad : ∀ u ∈ Ioo a b, (1 : ℝ) ≤ cost u := by
    intro u hu
    exact le_of_not_gt (fun h => hn ⟨u, hu, h⟩)
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b)
    hint hbad
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hm
  linarith

theorem exists_outer_two_error_point {a b p z : ℝ} (hab : a < b)
    (hp : 0 < p) (hz : 0 < z) (f g : ℝ → ℝ)
    (hint : IntervalIntegrable (fun u => |f u|/p+|g u|/z) volume a b)
    (hbudget : (∫ u in a..b, |f u|/p+|g u|/z) < b-a) :
    ∃ u ∈ Ioo a b, |f u| < p ∧ |g u| < z := by
  obtain ⟨u, hu, hcost⟩ := exists_outer_good_point hab hint hbudget
  have hf0 := div_nonneg (abs_nonneg (f u)) hp.le
  have hg0 := div_nonneg (abs_nonneg (g u)) hz.le
  refine ⟨u, hu, ?_, ?_⟩
  · apply (div_lt_one₀ hp).mp
    linarith
  · apply (div_lt_one₀ hz).mp
    linarith

theorem outer_common_budget_of_absolute_budgets {a b p z : ℝ}
    (hab : a < b) (hp : 0 < p) (hz : 0 < z) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable (fun u => |f u|) volume a b)
    (hg : IntervalIntegrable (fun u => |g u|) volume a b)
    (hfsmall : (∫ u in a..b, |f u|) ≤ p*(b-a)/4)
    (hgsmall : (∫ u in a..b, |g u|) ≤ z*(b-a)/4) :
    IntervalIntegrable (fun u => |f u|/p+|g u|/z) volume a b ∧
    (∫ u in a..b, |f u|/p+|g u|/z) < b-a := by
  refine ⟨(hf.div_const p).add (hg.div_const z), ?_⟩
  rw [intervalIntegral.integral_add (hf.div_const p) (hg.div_const z),
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  have hfp : (∫ u in a..b, |f u|)/p ≤ (b-a)/4 :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  have hgp : (∫ u in a..b, |g u|)/z ≤ (b-a)/4 :=
    (div_le_iff₀ hz).mpr (by nlinarith)
  linarith

theorem outer_absolute_budget_of_square_budget {a b t : ℝ} (hab : a ≤ b)
    (ht : 0 < t) (f : ℝ → ℝ)
    (hf : IntervalIntegrable (fun u => |f u|) volume a b)
    (hf₂ : IntervalIntegrable (fun u => (f u)^2) volume a b)
    (hsmall : (∫ u in a..b, (f u)^2) ≤ t^2*(b-a)) :
    (∫ u in a..b, |f u|) ≤ t*(b-a) := by
  have hm := intervalIntegral.integral_mono_on hab (hf.const_mul (2*t))
    (hf₂.add (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => t^2) volume a b)) (by
      intro u _
      nlinarith [sq_nonneg (|f u|-t), sq_abs (f u)])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hf₂ intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hm
  nlinarith

theorem exists_two_outer_two_error_points {a₁ b₁ a₂ b₂ p z : ℝ}
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hp : 0 < p) (hz : 0 < z)
    (f g : ℝ → ℝ)
    (hi₁ : IntervalIntegrable (fun u => |f u|/p+|g u|/z) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun u => |f u|/p+|g u|/z) volume a₂ b₂)
    (hb₁ : (∫ u in a₁..b₁, |f u|/p+|g u|/z) < b₁-a₁)
    (hb₂ : (∫ u in a₂..b₂, |f u|/p+|g u|/z) < b₂-a₂) :
    ∃ u₁ ∈ Ioo a₁ b₁, ∃ u₂ ∈ Ioo a₂ b₂,
      (|f u₁| < p ∧ |g u₁| < z) ∧ (|f u₂| < p ∧ |g u₂| < z) := by
  obtain ⟨u₁, hu₁, hf₁, hg₁⟩ := exists_outer_two_error_point h₁ hp hz f g hi₁ hb₁
  obtain ⟨u₂, hu₂, hf₂, hg₂⟩ := exists_outer_two_error_point h₂ hp hz f g hi₂ hb₂
  exact ⟨u₁, hu₁, u₂, hu₂, ⟨hf₁, hg₁⟩, ⟨hf₂, hg₂⟩⟩

def wallMixedQuantile (T ε r S : ℝ) : ℝ := (ε*r+(T-ε)*S)/T

theorem wallMixedQuantile_sub_radius {T ε r S : ℝ} (hT : 0 < T) :
    wallMixedQuantile T ε r S-r = ((T-ε)/T)*(S-r) := by
  unfold wallMixedQuantile
  field_simp
  ring

theorem wallMixedQuantile_sub_mean {T ε r S : ℝ} (hT : 0 < T) :
    S-wallMixedQuantile T ε r S = (ε/T)*(S-r) := by
  unfold wallMixedQuantile
  field_simp
  ring

theorem wallMixedQuantile_radius_error {T ε r S : ℝ} (hT : 0 < T)
    (hε : 0 ≤ ε) (hεT : ε ≤ T) :
    |wallMixedQuantile T ε r S-r| ≤ |S-r| := by
  rw [wallMixedQuantile_sub_radius hT, abs_mul,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hεT) hT.le)]
  have hc : (T-ε)/T ≤ 1 := (div_le_one₀ hT).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans_eq (one_mul _)

theorem wallMixedQuantile_calibration_error {T ε r S x E δ : ℝ}
    (hT : 0 < T) (hx : 0 ≤ x) (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hεE : ε ≤ E*x^2) (herr : |S-r| ≤ δ*x) :
    |S-wallMixedQuantile T ε r S| ≤ (E*δ/T)*x^3 := by
  rw [wallMixedQuantile_sub_mean hT, abs_mul, abs_of_nonneg (div_nonneg hε hT.le)]
  have he := div_le_div_of_nonneg_right hεE hT.le
  have hm := mul_le_mul he herr (abs_nonneg _) (by positivity : 0 ≤ E*x^2/T)
  exact hm.trans_eq (by ring)

theorem actualMixedClock_high_wall {T ε r : ℝ} (n : ℕ) (b h : ℝ → ℝ≥0)
    (u : ℝ) (hb : (b u : ℝ)=T-ε) (hh : (h u : ℝ)=ε*r) :
    actualMixedClock n b h u/T = wallMixedQuantile T ε r (orderedPathS n b h u) := by
  simp only [actualMixedClock, wallMixedQuantile, hb, hh]

def actualCavityResidual {T : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (u : ℝ) : ℝ :=
  orderedPathS n b h u - scalarCovarianceResponse hT
    (actualMixedMassProfile hT n hn b h hb hh htotal) (actualMixedClock n b h u)

theorem actual_outer_calibration_points
    {T x E δ B A c₀ R₀ c₂ a₁ b₁ a₂ b₂ : ℝ} (hT : 0 < T) (hx : 0 < x)
    (e : ℝ → ℝ)
    (hε : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, 0 ≤ e u)
    (hεT : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ T)
    (hE : 0 ≤ E) (hεE : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ E*x^2)
    (hδ : 0 < δ) (hB : 0 < B) (hsep : R₀+2*δ < c₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1)
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (hmass : b₂ ≤ A*x)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (r : ℝ → ℝ)
    (hwallb : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (b u : ℝ)=T-e u)
    (hwallh : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (h u : ℝ)=e u*r u)
    (hr₁ : ∀ u ∈ Ioo a₁ b₁, c₀*x ≤ r u ∧ r u ≤ R₀*x)
    (hr₂ : ∀ u ∈ Ioo a₂ b₂, c₂*x ≤ r u)
    (hi₁ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₂ b₂)
    (hbudget₁ : (∫ u in a₁..b₁, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₁-a₁)
    (hbudget₂ : (∫ u in a₂..b₂, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₂-a₂) :
    let α := actualMixedMassProfile hT n hn b h hb hh htotal
    ∃ u₁ ∈ Ioo a₁ b₁, ∃ u₂ ∈ Ioo a₂ b₂,
      let q₁ := actualMixedClock n b h u₁/T
      let q₂ := actualMixedClock n b h u₂/T
      (c₀-δ)*x ≤ q₁ ∧ q₁ ≤ (R₀+δ)*x ∧ q₁ < q₂ ∧
      α.val q₁ ≤ A*x ∧
      |scalarPlantedEnergy hT α q₁-q₁| ≤ (B+E*δ/T)*x^3 := by
  dsimp only
  let α := actualMixedMassProfile hT n hn b h hb hh htotal
  obtain ⟨u₁, hu₁, u₂, hu₂, hgood₁, hgood₂⟩ :=
    exists_two_outer_two_error_points hab₁ hab₂ (mul_pos hδ hx)
      (mul_pos hB (pow_pos hx 3)) (fun u => orderedPathS n b h u-r u)
      (actualCavityResidual hT n hn b h hb hh htotal) hi₁ hi₂ hbudget₁ hbudget₂
  let q₁ := actualMixedClock n b h u₁/T
  let q₂ := actualMixedClock n b h u₂/T
  have he₁ : q₁ = wallMixedQuantile T (e u₁) (r u₁) (orderedPathS n b h u₁) :=
    actualMixedClock_high_wall n b h u₁ (hwallb u₁ (Or.inl hu₁)) (hwallh u₁ (Or.inl hu₁))
  have he₂ : q₂ = wallMixedQuantile T (e u₂) (r u₂) (orderedPathS n b h u₂) :=
    actualMixedClock_high_wall n b h u₂ (hwallb u₂ (Or.inr hu₂)) (hwallh u₂ (Or.inr hu₂))
  have herr₁ : |q₁-r u₁| < δ*x := by
    rw [he₁]
    exact (wallMixedQuantile_radius_error hT (hε u₁ (Or.inl hu₁))
      (hεT u₁ (Or.inl hu₁))).trans_lt hgood₁.1
  have herr₂ : |q₂-r u₂| < δ*x := by
    rw [he₂]
    exact (wallMixedQuantile_radius_error hT (hε u₂ (Or.inr hu₂))
      (hεT u₂ (Or.inr hu₂))).trans_lt hgood₂.1
  have hlow : (c₀-δ)*x ≤ q₁ := by
    have hl := (abs_lt.mp herr₁).1
    have hr := (hr₁ u₁ hu₁).1
    nlinarith
  have hhigh : q₁ ≤ (R₀+δ)*x := by
    have hl := (abs_lt.mp herr₁).2
    have hr := (hr₁ u₁ hu₁).2
    nlinarith
  have horder : q₁ < q₂ := by
    have hl := (abs_lt.mp herr₂).1
    have hr := hr₂ u₂ hu₂
    have hs := mul_lt_mul_of_pos_right hsep hx
    nlinarith
  have hu₂' : u₂ ∈ Ioc (0 : ℝ) 1 := ⟨ha₂.trans_lt hu₂.1, hu₂.2.le.trans hb₂⟩
  have hcdf : α.val q₁ ≤ A*x := by
    have hc := actualMixedMassProfile_cdf_cap hT n hn b h hb hh htotal hu₂' horder
    exact hc.trans ((hu₂.2.le.trans hmass))
  have hmean : |orderedPathS n b h u₁-q₁| ≤ (E*δ/T)*x^3 := by
    rw [he₁]
    exact wallMixedQuantile_calibration_error hT hx.le hE hδ.le
      (hε u₁ (Or.inl hu₁)) (hεE u₁ (Or.inl hu₁)) hgood₁.1.le
  have hcavity : |scalarPlantedEnergy hT α q₁-orderedPathS n b h u₁| ≤ B*x^3 := by
    rw [abs_sub_comm]
    exact hgood₁.2.le
  have hcal : |scalarPlantedEnergy hT α q₁-q₁| ≤ (B+E*δ/T)*x^3 := by
    have ht := abs_add_le (scalarPlantedEnergy hT α q₁-orderedPathS n b h u₁)
      (orderedPathS n b h u₁-q₁)
    have he : scalarPlantedEnergy hT α q₁-orderedPathS n b h u₁+
      (orderedPathS n b h u₁-q₁) = scalarPlantedEnergy hT α q₁-q₁ := by ring
    rw [he] at ht
    exact (ht.trans (add_le_add hcavity hmean)).trans_eq (by ring)
  exact ⟨u₁, hu₁, u₂, hu₂, hlow, hhigh, horder, hcdf, hcal⟩

def outerCalibrationUniformConstant (T A R c B : ℝ) : ℝ :=
  ((B+T^2*scalarSmallClockFluxConstant T A R*R^2)/c)*R+
    T^2*scalarSmallClockFluxConstant T A R*R^2

theorem actual_outer_budgets_low_clock_uniform
    {T x E δ B A c₀ R₀ c₂ a₁ b₁ a₂ b₂ : ℝ} (hT : 0 < T) (hx : 0 < x)
    (e : ℝ → ℝ)
    (hε : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, 0 ≤ e u)
    (hεT : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ T)
    (hE : 0 ≤ E) (hεE : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ E*x^2)
    (hδ : 0 < δ) (hB : 0 < B) (hsep : R₀+2*δ < c₂)
    (hcδ : δ < c₀) (hR₀ : 0 ≤ R₀) (hA : 0 ≤ A)
    (hsmall : T*(R₀+δ)*x ≤ 1)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1)
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (hmass : b₂ ≤ A*x)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (r : ℝ → ℝ)
    (hwallb : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (b u : ℝ)=T-e u)
    (hwallh : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (h u : ℝ)=e u*r u)
    (hr₁ : ∀ u ∈ Ioo a₁ b₁, c₀*x ≤ r u ∧ r u ≤ R₀*x)
    (hr₂ : ∀ u ∈ Ioo a₂ b₂, c₂*x ≤ r u)
    (hi₁ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₂ b₂)
    (hbudget₁ : (∫ u in a₁..b₁, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₁-a₁)
    (hbudget₂ : (∫ u in a₂..b₂, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₂-a₂) :
    let α := actualMixedMassProfile hT n hn b h hb hh htotal
    ∀ K, 0 ≤ K → K ≤ T*(c₀-δ)*x →
      |scalarCovarianceResponse hT α K-K/T| ≤
        outerCalibrationUniformConstant T A (R₀+δ) (c₀-δ) (B+E*δ/T)*x^3 := by
  dsimp only
  obtain ⟨u₁, hu₁, u₂, hu₂, hlow, hhigh, horder, hcdf, hcal⟩ :=
    actual_outer_calibration_points hT hx e hε hεT hE hεE hδ hB hsep
      ha₁ ha₂ hb₁ hb₂ hab₁ hab₂ hmass n hn b h hb hh htotal r
      hwallb hwallh hr₁ hr₂ hi₁ hi₂ hbudget₁ hbudget₂
  let α := actualMixedMassProfile hT n hn b h hb hh htotal
  let q := actualMixedClock n b h u₁/T
  have hup : u₁ ∈ Ioc (0 : ℝ) 1 := ⟨ha₁.trans_lt hu₁.1, hu₁.2.le.trans hb₁⟩
  have hq₁ : q ≤ 1 := by
    have hq := actualScalarClockQuantile_bounds hT n hn b h hb hh htotal u₁
      ⟨hup.1.le, hup.2⟩
    rw [actualScalarClockQuantile_on n b h hup.1] at hq
    exact hq.2
  have hTq : T*q ≤ 1 := by
    calc
      T*q ≤ T*((R₀+δ)*x) := mul_le_mul_of_nonneg_left hhigh hT.le
      _ = T*(R₀+δ)*x := by ring
      _ ≤ 1 := hsmall
  have hB' : 0 ≤ B+E*δ/T := add_nonneg hB.le (by positivity)
  have hc : 0 < c₀-δ := sub_pos.mpr hcδ
  have hR : 0 ≤ R₀+δ := add_nonneg hR₀ hδ.le
  intro K hK hKlow
  have hKq : K ≤ T*q := by
    have ht := mul_le_mul_of_nonneg_left hlow hT.le
    nlinarith
  exact scalarCovarianceResponse_calibrated_uniform hT α hx hA hR hc hB'
    hlow hhigh hq₁ hTq hcdf
    (fun s _ => actualMixedMassProfile_right_continuous hT n hn b h hb hh htotal s)
    hcal hK hKq

theorem actual_outer_budgets_origin_derivative
    {T x E δ B A c₀ R₀ c₂ a₁ b₁ a₂ b₂ : ℝ} (hT : 0 < T) (hx : 0 < x)
    (e : ℝ → ℝ)
    (hε : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, 0 ≤ e u)
    (hεT : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ T)
    (hE : 0 ≤ E) (hεE : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ E*x^2)
    (hδ : 0 < δ) (hB : 0 < B) (hsep : R₀+2*δ < c₂)
    (hcδ : δ < c₀) (hR₀ : 0 ≤ R₀) (hA : 0 ≤ A)
    (hsmall : T*(R₀+δ)*x ≤ 1)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1)
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (hmass : b₂ ≤ A*x)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (r : ℝ → ℝ)
    (hwallb : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (b u : ℝ)=T-e u)
    (hwallh : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (h u : ℝ)=e u*r u)
    (hr₁ : ∀ u ∈ Ioo a₁ b₁, c₀*x ≤ r u ∧ r u ≤ R₀*x)
    (hr₂ : ∀ u ∈ Ioo a₂ b₂, c₂*x ≤ r u)
    (hi₁ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₂ b₂)
    (hbudget₁ : (∫ u in a₁..b₁, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₁-a₁)
    (hbudget₂ : (∫ u in a₂..b₂, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₂-a₂) :
    let α := actualMixedMassProfile hT n hn b h hb hh htotal
    HasDerivWithinAt (scalarCovarianceResponse hT α)
      (scalarPlantedCurvature hT α 0) (Ici 0) 0 ∧
    |scalarPlantedCurvature hT α 0-1/T| ≤
      (((B+E*δ/T+T^2*scalarSmallClockFluxConstant T A (R₀+δ)*(R₀+δ)^2)/(c₀-δ))*x^2)/T := by
  dsimp only
  obtain ⟨u₁, hu₁, u₂, hu₂, hlow, hhigh, horder, hcdf, hcal⟩ :=
    actual_outer_calibration_points hT hx e hε hεT hE hεE hδ hB hsep
      ha₁ ha₂ hb₁ hb₂ hab₁ hab₂ hmass n hn b h hb hh htotal r
      hwallb hwallh hr₁ hr₂ hi₁ hi₂ hbudget₁ hbudget₂
  let α := actualMixedMassProfile hT n hn b h hb hh htotal
  let q := actualMixedClock n b h u₁/T
  have hup : u₁ ∈ Ioc (0 : ℝ) 1 := ⟨ha₁.trans_lt hu₁.1, hu₁.2.le.trans hb₁⟩
  have hq₁ : q ≤ 1 := by
    have hq := actualScalarClockQuantile_bounds hT n hn b h hb hh htotal u₁
      ⟨hup.1.le, hup.2⟩
    rw [actualScalarClockQuantile_on n b h hup.1] at hq
    exact hq.2
  have hTq : T*q ≤ 1 := by
    calc
      T*q ≤ T*((R₀+δ)*x) := mul_le_mul_of_nonneg_left hhigh hT.le
      _ = T*(R₀+δ)*x := by ring
      _ ≤ 1 := hsmall
  have hB' : 0 ≤ B+E*δ/T := add_nonneg hB.le (by positivity)
  have hc : 0 < c₀-δ := sub_pos.mpr hcδ
  have hR : 0 ≤ R₀+δ := add_nonneg hR₀ hδ.le
  refine ⟨scalarCovarianceResponse_origin_derivative hT α
    (fun s _ => actualMixedMassProfile_right_continuous hT n hn b h hb hh htotal s), ?_⟩
  have hslope := scalarPlantedEnergy_calibrated_slope hT α hx hA hR hc hB'
    hlow hhigh hq₁ hTq hcdf
    (fun s _ => actualMixedMassProfile_right_continuous hT n hn b h hb hh htotal s) hcal
  apply (le_div_iff₀ hT).mpr
  have he : T*scalarPlantedCurvature hT α 0-1 =
      T*(scalarPlantedCurvature hT α 0-1/T) := by field_simp
  rw [he, abs_mul, abs_of_pos hT] at hslope
  simpa only [mul_comm] using hslope

theorem actual_outer_budgets_below_band_uniform
    {T x E δ B A c₀ R₀ c₂ a₁ b₁ a₂ b₂ : ℝ} (hT : 0 < T) (hx : 0 < x)
    (e : ℝ → ℝ)
    (hε : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, 0 ≤ e u)
    (hεT : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ T)
    (hE : 0 ≤ E) (hεE : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ E*x^2)
    (hδ : 0 < δ) (hB : 0 < B) (hsep : R₀+2*δ < c₂)
    (hcδ : δ < c₀) (hR₀ : 0 ≤ R₀) (hA : 0 ≤ A)
    (hsmall : T*(R₀+δ)*x ≤ 1)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1)
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (hmass : b₂ ≤ A*x)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (r : ℝ → ℝ)
    (hwallb : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (b u : ℝ)=T-e u)
    (hwallh : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (h u : ℝ)=e u*r u)
    (hr₁ : ∀ u ∈ Ioo a₁ b₁, c₀*x ≤ r u ∧ r u ≤ R₀*x)
    (hr₂ : ∀ u ∈ Ioo a₂ b₂, c₂*x ≤ r u)
    (hi₁ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₂ b₂)
    (hbudget₁ : (∫ u in a₁..b₁, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₁-a₁)
    (hbudget₂ : (∫ u in a₂..b₂, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₂-a₂) :
    let α := actualMixedMassProfile hT n hn b h hb hh htotal
    ∀ u, u ∈ Ioc (0 : ℝ) 1 → u ≤ a₁ →
      actualMixedClock n b h u ≤ T*(R₀+δ)*x ∧
      |scalarCovarianceResponse hT α (actualMixedClock n b h u)-actualMixedClock n b h u/T| ≤
        outerCalibrationUniformConstant T A (R₀+δ) (c₀-δ) (B+E*δ/T)*x^3 := by
  dsimp only
  obtain ⟨u₁, hu₁, u₂, hu₂, hlow, hhigh, horder, hcdf, hcal⟩ :=
    actual_outer_calibration_points hT hx e hε hεT hE hεE hδ hB hsep
      ha₁ ha₂ hb₁ hb₂ hab₁ hab₂ hmass n hn b h hb hh htotal r
      hwallb hwallh hr₁ hr₂ hi₁ hi₂ hbudget₁ hbudget₂
  let α := actualMixedMassProfile hT n hn b h hb hh htotal
  let q := actualMixedClock n b h u₁/T
  have hup : u₁ ∈ Ioc (0 : ℝ) 1 := ⟨ha₁.trans_lt hu₁.1, hu₁.2.le.trans hb₁⟩
  have hq₁ : q ≤ 1 := by
    have hq := actualScalarClockQuantile_bounds hT n hn b h hb hh htotal u₁
      ⟨hup.1.le, hup.2⟩
    rw [actualScalarClockQuantile_on n b h hup.1] at hq
    exact hq.2
  have hTq : T*q ≤ 1 := by
    calc
      T*q ≤ T*((R₀+δ)*x) := mul_le_mul_of_nonneg_left hhigh hT.le
      _ = T*(R₀+δ)*x := by ring
      _ ≤ 1 := hsmall
  have hB' : 0 ≤ B+E*δ/T := add_nonneg hB.le (by positivity)
  have hc : 0 < c₀-δ := sub_pos.mpr hcδ
  have hR : 0 ≤ R₀+δ := add_nonneg hR₀ hδ.le
  intro u hu hulow
  have huu₁ : u ≤ u₁ := hulow.trans hu₁.1.le
  have hKq : actualMixedClock n b h u ≤ T*q := by
    have hm := actualMixedClock_monotone n hn b h hb hh hu hup huu₁
    have he : T*q = actualMixedClock n b h u₁ := by dsimp [q]; field_simp
    exact hm.trans_eq he.symm
  have hKbound : actualMixedClock n b h u ≤ T*(R₀+δ)*x := by
    have ht := mul_le_mul_of_nonneg_left hhigh hT.le
    nlinarith
  refine ⟨hKbound, ?_⟩
  exact scalarCovarianceResponse_calibrated_uniform hT α hx hA hR hc hB'
    hlow hhigh hq₁ hTq hcdf
    (fun s _ => actualMixedMassProfile_right_continuous hT n hn b h hb hh htotal s)
    hcal (actualMixedClock_bounds n hn b h hb hh hu).1 hKq

theorem actual_low_clock_mean_balance {T x B C Kmax : ℝ} (hT : 0 < T)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T)
    (hscalar : ∀ K, 0 ≤ K → K ≤ Kmax →
      |scalarCovarianceResponse hT (actualMixedMassProfile hT n hn b h hb hh htotal) K-K/T|
        ≤ C*x^3)
    {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (hK : actualMixedClock n b h u ≤ Kmax)
    (hres : |actualCavityResidual hT n hn b h hb hh htotal u| ≤ B*x^3) :
    |orderedPathS n b h u-actualMixedClock n b h u/T| ≤ (B+C)*x^3 ∧
    |(T-(b u : ℝ))*orderedPathS n b h u-(h u : ℝ)| ≤ T*(B+C)*x^3 := by
  let α := actualMixedMassProfile hT n hn b h hb hh htotal
  let K := actualMixedClock n b h u
  have hcal := hscalar K (actualMixedClock_bounds n hn b h hb hh hu).1 hK
  have ht := abs_add_le
    (orderedPathS n b h u-scalarCovarianceResponse hT α K)
    (scalarCovarianceResponse hT α K-K/T)
  have he : orderedPathS n b h u-scalarCovarianceResponse hT α K+
    (scalarCovarianceResponse hT α K-K/T) = orderedPathS n b h u-K/T := by ring
  rw [he] at ht
  have hmean : |orderedPathS n b h u-K/T| ≤ (B+C)*x^3 :=
    (ht.trans (add_le_add hres hcal)).trans_eq (by ring)
  refine ⟨hmean, ?_⟩
  have heq : (T-(b u : ℝ))*orderedPathS n b h u-(h u : ℝ) =
      T*(orderedPathS n b h u-K/T) := by
    dsimp [K, actualMixedClock]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos hT]
  exact (mul_le_mul_of_nonneg_left hmean hT.le).trans_eq (by ring)

theorem actual_low_wall_mean_suppression {T x B C ε θ cL H : ℝ} (hT : 0 < T)
    (hε : 0 < ε) (hθc : 0 ≤ θ*cL)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1)
    (hbu : (b u : ℝ)=T-ε-θ*cL) (hhu : (h u : ℝ) ≤ H*x^3)
    (hbalance : |(T-(b u : ℝ))*orderedPathS n b h u-(h u : ℝ)| ≤ T*(B+C)*x^3) :
    orderedPathS n b h u ≤ ((H+T*(B+C))*x^3)/ε := by
  have hS := (orderedPath_SK_bounds n hn b h hb hh hu).1
  have hupper := (le_abs_self ((T-(b u : ℝ))*orderedPathS n b h u-(h u : ℝ))).trans hbalance
  rw [hbu] at hupper
  apply (le_div_iff₀ hε).mpr
  have hnonneg := mul_nonneg hθc hS
  nlinarith

theorem actual_outer_budgets_low_wall_mean
    {T x E δ B A c₀ R₀ c₂ a₁ b₁ a₂ b₂ : ℝ} (hT : 0 < T) (hx : 0 < x)
    (e : ℝ → ℝ)
    (hε : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, 0 ≤ e u)
    (hεT : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ T)
    (hE : 0 ≤ E) (hεE : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ E*x^2)
    (hδ : 0 < δ) (hB : 0 < B) (hsep : R₀+2*δ < c₂)
    (hcδ : δ < c₀) (hR₀ : 0 ≤ R₀) (hA : 0 ≤ A)
    (hsmall : T*(R₀+δ)*x ≤ 1)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1)
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (hmass : b₂ ≤ A*x)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (r : ℝ → ℝ)
    (hwallb : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (b u : ℝ)=T-e u)
    (hwallh : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (h u : ℝ)=e u*r u)
    (hr₁ : ∀ u ∈ Ioo a₁ b₁, c₀*x ≤ r u ∧ r u ≤ R₀*x)
    (hr₂ : ∀ u ∈ Ioo a₂ b₂, c₂*x ≤ r u)
    (hi₁ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₂ b₂)
    (hbudget₁ : (∫ u in a₁..b₁, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₁-a₁)
    (hbudget₂ : (∫ u in a₂..b₂, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₂-a₂)
    {u ε θ cL H B_low : ℝ} (hεlow : 0 < ε) (hθc : 0 ≤ θ*cL)
    (hu : u ∈ Ioc (0 : ℝ) 1) (hbu : (b u : ℝ)=T-ε-θ*cL)
    (hhu : (h u : ℝ) ≤ H*x^3) (hKlow : actualMixedClock n b h u ≤ T*(c₀-δ)*x)
    (hlowres : |actualCavityResidual hT n hn b h hb hh htotal u| ≤ B_low*x^3) :
    orderedPathS n b h u ≤
      ((H+T*(B_low+outerCalibrationUniformConstant T A (R₀+δ) (c₀-δ) (B+E*δ/T)))*x^3)/ε := by
  have hscalar := actual_outer_budgets_low_clock_uniform hT hx e hε hεT hE hεE
    hδ hB hsep hcδ hR₀ hA hsmall ha₁ ha₂ hb₁ hb₂ hab₁ hab₂ hmass n hn b h
    hb hh htotal r hwallb hwallh hr₁ hr₂ hi₁ hi₂ hbudget₁ hbudget₂
  have hbalance := (actual_low_clock_mean_balance hT n hn b h hb hh htotal
    hscalar hu hKlow hlowres).2
  exact actual_low_wall_mean_suppression hT hεlow hθc n hn b h hb hh hu hbu hhu hbalance

theorem actualMixedClock_balance_of_mean_error {T x C : ℝ} (hT : 0 < T)
    (n : ℕ) (b h : ℝ → ℝ≥0) (u : ℝ)
    (hmean : |orderedPathS n b h u-actualMixedClock n b h u/T| ≤ C*x^3) :
    |(T-(b u : ℝ))*orderedPathS n b h u-(h u : ℝ)| ≤ T*C*x^3 := by
  have heq : (T-(b u : ℝ))*orderedPathS n b h u-(h u : ℝ) =
      T*(orderedPathS n b h u-actualMixedClock n b h u/T) := by
    unfold actualMixedClock
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos hT]
  exact (mul_le_mul_of_nonneg_left hmean hT.le).trans_eq (by ring)

theorem actual_outer_budgets_omitted_wall_mean
    {T x E δ B A c₀ R₀ c₂ a₁ b₁ a₂ b₂ : ℝ} (hT : 0 < T) (hx : 0 < x)
    (e : ℝ → ℝ)
    (hε : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, 0 ≤ e u)
    (hεT : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ T)
    (hE : 0 ≤ E) (hεE : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, e u ≤ E*x^2)
    (hδ : 0 < δ) (hB : 0 < B) (hsep : R₀+2*δ < c₂)
    (hcδ : δ < c₀) (hR₀ : 0 ≤ R₀) (hA : 0 ≤ A)
    (hsmall : T*(R₀+δ)*x ≤ 1)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1)
    (hab₁ : a₁ < b₁) (hab₂ : a₂ < b₂) (hmass : b₂ ≤ A*x)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1, (h u : ℝ)+(b u : ℝ) ≤ T) (r : ℝ → ℝ)
    (hwallb : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (b u : ℝ)=T-e u)
    (hwallh : ∀ u ∈ Ioo a₁ b₁ ∪ Ioo a₂ b₂, (h u : ℝ)=e u*r u)
    (hr₁ : ∀ u ∈ Ioo a₁ b₁, c₀*x ≤ r u ∧ r u ≤ R₀*x)
    (hr₂ : ∀ u ∈ Ioo a₂ b₂, c₂*x ≤ r u)
    (hi₁ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₁ b₁)
    (hi₂ : IntervalIntegrable (fun u => |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) volume a₂ b₂)
    (hbudget₁ : (∫ u in a₁..b₁, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₁-a₁)
    (hbudget₂ : (∫ u in a₂..b₂, |orderedPathS n b h u-r u|/(δ*x)+
      |actualCavityResidual hT n hn b h hb hh htotal u|/(B*x^3)) < b₂-a₂)
    {u ε θ cL H B_low : ℝ} (hεlow : 0 < ε) (hθc : 0 ≤ θ*cL)
    (hu : u ∈ Ioc (0 : ℝ) 1) (hbu : (b u : ℝ)=T-ε-θ*cL)
    (hhu : (h u : ℝ) ≤ H*x^3) (hulow : u ≤ a₁)
    (hlowres : |actualCavityResidual hT n hn b h hb hh htotal u| ≤ B_low*x^3) :
    orderedPathS n b h u ≤
      ((H+T*(B_low+outerCalibrationUniformConstant T A (R₀+δ) (c₀-δ) (B+E*δ/T)))*x^3)/ε := by
  let α := actualMixedMassProfile hT n hn b h hb hh htotal
  let C := outerCalibrationUniformConstant T A (R₀+δ) (c₀-δ) (B+E*δ/T)
  have hcal := (actual_outer_budgets_below_band_uniform hT hx e hε hεT hE hεE
    hδ hB hsep hcδ hR₀ hA hsmall ha₁ ha₂ hb₁ hb₂ hab₁ hab₂ hmass n hn b h
    hb hh htotal r hwallb hwallh hr₁ hr₂ hi₁ hi₂ hbudget₁ hbudget₂ u hu hulow).2
  have ht := abs_add_le
    (orderedPathS n b h u-scalarCovarianceResponse hT α (actualMixedClock n b h u))
    (scalarCovarianceResponse hT α (actualMixedClock n b h u)-actualMixedClock n b h u/T)
  have he : orderedPathS n b h u-scalarCovarianceResponse hT α (actualMixedClock n b h u)+
    (scalarCovarianceResponse hT α (actualMixedClock n b h u)-actualMixedClock n b h u/T) =
      orderedPathS n b h u-actualMixedClock n b h u/T := by ring
  rw [he] at ht
  have hmean : |orderedPathS n b h u-actualMixedClock n b h u/T| ≤ (B_low+C)*x^3 :=
    (ht.trans (add_le_add hlowres hcal)).trans_eq (by ring)
  have hbalance := actualMixedClock_balance_of_mean_error hT n b h u hmean
  exact actual_low_wall_mean_suppression hT hεlow hθc n hn b h hb hh hu hbu hhu hbalance

end OAI.SKFluctuations.LaplaceWindowFormalization
