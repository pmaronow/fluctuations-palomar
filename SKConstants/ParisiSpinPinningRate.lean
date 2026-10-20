module
public import SKConstants.ParisiSpinPinningConcentration
public import SKConstants.Asymptotics

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem pinning_bernstein_eventually_stretched (r s : ℝ) (hrs : r<s) (hs : s<1) :
    ∀ᶠ n : ℕ in atTop, 2*Real.exp (-(n:ℝ)*(n:ℝ)^(-r)/8)≤
      Real.exp (-(n:ℝ)^(1-s)) := by
  have hp := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually
    (eventually_ge_atTop (16:ℝ))
  have hl := (tendsto_rpow_atTop (show 0<1-s by linarith)).eventually
    (eventually_ge_atTop (Real.log 2))
  have hreal : ∀ᶠ x : ℝ in atTop, 2*Real.exp (-x*x^(-r)/8)≤Real.exp (-x^(1-s)) := by
    filter_upwards [hp,hl,eventually_gt_atTop (0:ℝ)] with x hp hl hx
    have he1 : x*x^(-r)=x^(1-r) := by
      calc
        _ = x^(1:ℝ)*x^(-r) := by rw [Real.rpow_one]
        _ = _ := by simpa only [sub_eq_add_neg] using (Real.rpow_add hx (1:ℝ) (-r)).symm
    have he2 : x^(1-r)=x^(s-r)*x^(1-s) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have hexp : -x*x^(-r)/8≤-2*x^(1-s) := by
      rw [neg_mul,he1,he2]
      nlinarith [mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hx.le (1-s))]
    calc
      _ ≤ 2*Real.exp (-2*x^(1-s)) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexp) (by norm_num)
      _ = Real.exp (Real.log 2)*Real.exp (-2*x^(1-s)) := by
        rw [Real.exp_log (by norm_num : (0:ℝ)<2)]
      _ = Real.exp (Real.log 2-2*x^(1-s)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact tendsto_natCast_atTop_atTop.eventually hreal

theorem pinning_log_time_eventually_small (B r : ℝ) (hB : 0<B) (hr : r<B/2) :
    ∀ᶠ n : ℕ in atTop,
      1≤(B*Real.log (n:ℝ)).toNNReal ∧
      8*Real.exp (-((B*Real.log (n:ℝ)).toNNReal:ℝ)/2)≤(n:ℝ)^(-r) := by
  have hlog := (Filter.Tendsto.const_mul_atTop hB Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1:ℝ))
  have hratio := (tendsto_rpow_neg_atTop (show 0<B/2-r by linarith)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/8))
  have hreal : ∀ᶠ x : ℝ in atTop,
      1≤(B*Real.log x).toNNReal ∧
      8*Real.exp (-((B*Real.log x).toNNReal:ℝ)/2)≤x^(-r) := by
    filter_upwards [hlog,hratio,eventually_gt_atTop (0:ℝ)] with x hlog hratio hx
    have hn : 0≤B*Real.log x := by linarith
    have ht : ((B*Real.log x).toNNReal:ℝ)=B*Real.log x := Real.coe_toNNReal _ hn
    refine ⟨by exact_mod_cast (show (1:ℝ)≤((B*Real.log x).toNNReal:ℝ) by rwa [ht]),?_⟩
    rw [ht]
    have he : Real.exp (-(B*Real.log x)/2)=x^(-B/2) := by
      rw [Real.rpow_def_of_pos hx]
      congr 1
      ring
    rw [he]
    have hp : x^(-B/2)=x^(-(B/2-r))*x^(-r) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_right hratio.le (Real.rpow_nonneg hx.le (-r))]
  exact tendsto_natCast_atTop_atTop.eventually hreal

theorem actualParisiPinning_eventually_stretched {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (B r s : ℝ) (hB : 0<B) (hrB : r<B/2) (hrs : r<s) (hs : s<1)
    (T : ℕ → ℝ≥0)
    (hT : ∀ᶠ n : ℕ in atTop,
      parisiEquilibriumPhysicalEndpoint β+(B*Real.log (n:ℝ)).toNNReal≤T n) :
    ∀ᶠ n : ℕ in atTop,
      (actualParisiTerminalSpinRowsLaw W β (T n) n).real
        {ω | 2*(n:ℝ)^(-r)≤(∑ i : Fin n,actualParisiPinningError W β
          (parisiEquilibriumPhysicalEndpoint β+(B*Real.log (n:ℝ)).toNNReal) (ω i))/(n:ℝ)}≤
        Real.exp (-(n:ℝ)^(1-s)) := by
  filter_upwards [pinning_log_time_eventually_small B r hB hrB,
    pinning_bernstein_eventually_stretched r s hrs hs,hT,eventually_gt_atTop 0]
    with n hsmall htail hT hn
  have hnR : (0:ℝ)<(n:ℝ) := by exact_mod_cast hn
  exact (actualParisiPinning_iid_tail_exp W β hβ _ _ hsmall.1 hT n hn
    ((n:ℝ)^(-r)) (Real.rpow_pos_of_pos hnR _) hsmall.2).trans htail

end SKConstants
