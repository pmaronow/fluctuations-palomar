module

public import SKConstants.ParisiExpectedRegularContinuity

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

variable (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z∈Icc (0:ℝ) 1)
  (h1 : α 1=1) (hβ : β≠0) {T : ℝ} (hT0 : 0≤T) (hT1 : T<1)

def compactCDFValue (β : ℝ) (α : ℝ → ℝ) (T t x : ℝ) : ℝ :=
  scalarCDFValue β α (cdfStripTime T t) (Real.toNNReal (1-cdfStripTime T t)) x

include ha hβ hT0 hT1 in
lemma compactCDFValue_smooth (t : ℝ) : ContDiff ℝ ∞ (compactCDFValue β α T t) := by
  have hq := cdfStripTime_mem hT0 t
  apply (scalarCDFValue_contDiff_and_higher_derivative_limit ha α.mono hβ _ _ ?_ ?_).1
  · rw [Real.coe_toNNReal _ (by linarith [hq.2,hT1])]
    linarith [hq.2,hT1]
  · rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [hq.1]

include ha hT0 in
lemma compactCDFValue_deriv_eq (t : ℝ) :
    deriv (compactCDFValue β α T t)=compactCDFGradient β α T t := by
  funext x
  exact (scalarCDFValue_hasDerivAt β ha α.mono _ _
    (by rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [(cdfStripTime_mem hT0 t).1]) x).deriv

include ha hT0 in
lemma compactCDFValue_lipschitz (t : ℝ) : LipschitzWith 1 (compactCDFValue β α T t) :=
  scalarCDFValue_lipschitz β ha α.mono _ _
    (by rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [(cdfStripTime_mem hT0 t).1])

lemma cdfStripTime_lipschitz (T : ℝ) : LipschitzWith 1 (cdfStripTime T) :=
  (LipschitzWith.id.min_const T).const_max 0

include ha h1 hβ hT1 in
lemma compactCDFValue_integral_rate {a b : ℝ} (ha0 : 0≤a) (hab : a≤b) (hbT : b≤T) (x : ℝ) :
    compactCDFValue β α T b x-compactCDFValue β α T a x=
      ∫ r in a..b, compactCDFValueRate β α T r x := by
  unfold compactCDFValue
  rw [cdfStripTime_eq ⟨ha0,hab.trans hbT⟩,cdfStripTime_eq ⟨ha0.trans hab,hbT⟩,
    scalarCDFValue_integral_time_equation β α ha h1 hβ ha0 hab (hbT.trans_lt hT1)]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hab] at hr
  exact (compactCDFValueRate_eq β α ha hT1.le
    ⟨ha0.trans hr.1,hr.2.trans hbT⟩ x).symm

include ha h1 hβ hT0 hT1 in
lemma compactCDFValue_time_lipschitz : ∃ C : ℝ≥0, ∀ s t x,
    |compactCDFValue β α T t x-compactCDFValue β α T s x|≤(C:ℝ)*|t-s| := by
  obtain ⟨C,hC⟩ := (compactCDFValueRate_family β α ha h1 hβ hT0 hT1).bound
  have hb {s t : ℝ} (hs : s∈Icc (0:ℝ) T) (ht : t∈Icc (0:ℝ) T) (hst : s≤t) (x : ℝ) :
      |compactCDFValue β α T t x-compactCDFValue β α T s x|≤(C:ℝ)*|t-s| := by
    rw [compactCDFValue_integral_rate β α ha h1 hβ hT1 hs.1 hst ht.2]
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun r => compactCDFValueRate β α T r x) (C:=(C:ℝ))
      (fun r _ => by simpa only [Real.norm_eq_abs] using hC r x)
  refine ⟨C,fun s t x => ?_⟩
  let u := cdfStripTime T s
  let v := cdfStripTime T t
  have hu := cdfStripTime_mem hT0 s
  have hv := cdfStripTime_mem hT0 t
  have HL : |v-u|≤|t-s| := by simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul] using
    (cdfStripTime_lipschitz T).norm_sub_le t s
  have HE : |compactCDFValue β α T t x-compactCDFValue β α T s x|≤(C:ℝ)*|v-u| := by
    have he (r : ℝ) : compactCDFValue β α T (cdfStripTime T r)=compactCDFValue β α T r := by
      unfold compactCDFValue
      rw [cdfStripTime_eq (cdfStripTime_mem hT0 r)]
    rcases le_total u v with huv|hvu
    · simpa only [he] using hb hu hv huv x
    · simpa only [he,abs_sub_comm] using hb hv hu hvu x
  exact HE.trans (mul_le_mul_of_nonneg_left HL C.coe_nonneg)

end SKConstants.ParisiFullSupport
