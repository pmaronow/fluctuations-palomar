module

public import ComparisonScalarSupportZeros
public import Mathlib.Topology.Order.Monotone

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 2200000
variable {Ω : Type*} [MeasurableSpace Ω]

def comparisonClockCDF (μ : Measure Ω) (q : Ω→ℝ) (t : ℝ) : ℝ :=
  μ.real {w | q w≤t}

theorem comparison_clock_cdf_sandwich (μ : Measure Ω) [IsFiniteMeasure μ]
    (q r : Ω→ℝ) (hi : Integrable (fun w=>|q w-r w|) μ) {t eps : ℝ}
    (heps : 0<eps) :
    comparisonClockCDF μ q t≤comparisonClockCDF μ r (t+eps)+(∫w,|q w-r w|∂μ)/eps := by
  have hsub : {w | q w≤t}⊆{w | r w≤t+eps}∪{w | eps≤|q w-r w|} := by
    intro w hw
    change q w≤t at hw
    by_cases hr : r w≤t+eps
    · exact Or.inl hr
    · right
      exact le_trans (by linarith : eps≤r w-q w) (le_abs_self _ |>.trans_eq (abs_sub_comm _ _))
  have hm := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun w=>abs_nonneg (q w-r w)) hi eps
  have hmark : μ.real {w | eps≤|q w-r w|}≤(∫w,|q w-r w|∂μ)/eps :=
    (le_div_iff₀ heps).mpr (by simpa only [mul_comm] using hm)
  exact (measureReal_mono (μ:=μ) hsub).trans ((measureReal_union_le _ _).trans (add_le_add le_rfl hmark))

theorem comparison_clock_cdf_limit_sandwich
    (μ : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (μ n))
    (q r : ℕ→Ω→ℝ) (U V : ℝ→ℝ)
    (hi : ∀n,Integrable (fun w=>|q n w-r n w|) (μ n))
    (hz : Tendsto (fun n=>∫w,|q n w-r n w|∂μ n) atTop (𝓝 0))
    (hU : ∀t,Tendsto (fun n=>comparisonClockCDF (μ n) (q n) t) atTop (𝓝 (U t)))
    (hV : ∀t,Tendsto (fun n=>comparisonClockCDF (μ n) (r n) t) atTop (𝓝 (V t)))
    {t eps : ℝ} (heps : 0<eps) : V (t-eps)≤U t ∧ U t≤V (t+eps) := by
  have hup : U t≤V (t+eps) := by
    have hl := (hV (t+eps)).add (hz.div_const eps)
    simp only [zero_div,add_zero] at hl
    exact le_of_tendsto_of_tendsto (hU t) hl (Eventually.of_forall fun n=>by
      let _ := hfinite n
      exact comparison_clock_cdf_sandwich (μ n) (q n) (r n) (hi n) heps)
  have hrev : ∀n,Integrable (fun w=>|r n w-q n w|) (μ n) := by
    intro n
    simpa only [abs_sub_comm] using hi n
  have hlo : V (t-eps)≤U t := by
    have hl := (hU t).add (hz.div_const eps)
    simp only [zero_div,add_zero] at hl
    apply le_of_tendsto_of_tendsto (hV (t-eps)) hl
    apply Eventually.of_forall
    intro n
    let _ := hfinite n
    simpa only [sub_add_cancel,abs_sub_comm] using
      comparison_clock_cdf_sandwich (μ n) (r n) (q n) (hrev n) (t:=t-eps) heps
  exact ⟨hlo,hup⟩

theorem comparison_clock_cdf_limits_eq_at_continuity
    (μ : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (μ n))
    (q r : ℕ→Ω→ℝ) (U V : ℝ→ℝ)
    (hi : ∀n,Integrable (fun w=>|q n w-r n w|) (μ n))
    (hz : Tendsto (fun n=>∫w,|q n w-r n w|∂μ n) atTop (𝓝 0))
    (hU : ∀t,Tendsto (fun n=>comparisonClockCDF (μ n) (q n) t) atTop (𝓝 (U t)))
    (hV : ∀t,Tendsto (fun n=>comparisonClockCDF (μ n) (r n) t) atTop (𝓝 (V t)))
    {t : ℝ} (hc : ContinuousAt V t) : U t=V t := by
  let eps := fun j : ℕ=>1/((j:ℝ)+1)
  have hep : ∀j,0<eps j := by intro j;dsimp [eps];positivity
  have he0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hp : Tendsto (fun j=>V (t+eps j)) atTop (𝓝 (V t)) :=
    hc.tendsto.comp (by simpa using tendsto_const_nhds.add he0)
  have hm : Tendsto (fun j=>V (t-eps j)) atTop (𝓝 (V t)) :=
    hc.tendsto.comp (by simpa using tendsto_const_nhds.sub he0)
  exact le_antisymm
    (ge_of_tendsto hp (Eventually.of_forall fun j=>
      (comparison_clock_cdf_limit_sandwich μ hfinite q r U V hi hz hU hV (hep j)).2))
    (le_of_tendsto hm (Eventually.of_forall fun j=>
      (comparison_clock_cdf_limit_sandwich μ hfinite q r U V hi hz hU hV (hep j)).1))

theorem comparison_clock_cdf_limits_ae_eq
    (μ : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (μ n))
    (q r : ℕ→Ω→ℝ) (U V : ℝ→ℝ) (hVm : Monotone V)
    (hi : ∀n,Integrable (fun w=>|q n w-r n w|) (μ n))
    (hz : Tendsto (fun n=>∫w,|q n w-r n w|∂μ n) atTop (𝓝 0))
    (hU : ∀t,Tendsto (fun n=>comparisonClockCDF (μ n) (q n) t) atTop (𝓝 (U t)))
    (hV : ∀t,Tendsto (fun n=>comparisonClockCDF (μ n) (r n) t) atTop (𝓝 (V t))) :
    U=ᵐ[volume] V := by
  have hc : ∀ᵐ t : ℝ,ContinuousAt V t := by
    apply ae_iff.mpr
    exact hVm.countable_not_continuousAt.measure_zero volume
  exact hc.mono fun t ht=>comparison_clock_cdf_limits_eq_at_continuity μ hfinite q r U V hi hz hU hV ht

theorem comparison_clock_cdf_interval_mass (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : Ω→ℝ) (hq : Measurable q) {a b : ℝ} (hab : a≤b) :
    μ.real {w | a<q w ∧ q w≤b}=comparisonClockCDF μ q b-comparisonClockCDF μ q a := by
  have hs : {w | q w≤a}⊆{w | q w≤b} := fun w hw=>hw.trans hab
  have he : {w | a<q w ∧ q w≤b}={w | q w≤b}\{w | q w≤a} := by
    ext w
    simp only [Set.mem_sdiff,Set.mem_ofPred_eq,not_le]
    tauto
  rw [he,measureReal_sdiff hs (measurableSet_le hq measurable_const)]
  rfl

theorem comparison_clock_cdf_support_mass
    (μ : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (μ n))
    (q : ℕ→Ω→ℝ) (hq : ∀n,Measurable (q n)) (V : ℝ→ℝ)
    (hV : ∀s,Tendsto (fun n=>comparisonClockCDF (μ n) (q n) s) atTop (𝓝 (V s)))
    {t : ℝ} (hsupport : ∀eps : ℝ,0<eps→V (t-eps)<V (t+eps)) :
    ∀eps : ℝ,0<eps→∃c : ℝ,0<c ∧
      ∀ᶠ n in atTop,c≤(μ n).real {w | |q n w-t|<eps} := by
  intro eps heps
  have hd := hsupport (eps/2) (by positivity)
  let c := (V (t+eps/2)-V (t-eps/2))/2
  have hc : 0<c := by dsimp [c];linarith
  have hlim := (hV (t+eps/2)).sub (hV (t-eps/2))
  have hev := hlim.eventually (lt_mem_nhds (show c<V (t+eps/2)-V (t-eps/2) by dsimp [c];linarith))
  refine ⟨c,hc,?_⟩
  filter_upwards [hev] with n hn
  let _ := hfinite n
  have hid := comparison_clock_cdf_interval_mass (μ n) (q n) (hq n)
    (show t-eps/2≤t+eps/2 by linarith)
  have hsub : {w | t-eps/2<q n w ∧ q n w≤t+eps/2}⊆{w | |q n w-t|<eps} := by
    intro w hw
    change t-eps/2<q n w ∧ q n w≤t+eps/2 at hw
    change |q n w-t|<eps
    exact abs_lt.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
  exact (hn.le.trans_eq hid.symm).trans (measureReal_mono hsub)

end OAI.SKFluctuations.LaplaceWindowFormalization
