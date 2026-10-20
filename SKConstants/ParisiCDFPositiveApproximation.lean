module

public import SKConstants.ParisiGridApproximation
public import SKConstants.ParisiCDFCoefficientJets

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def positiveStieltjesCDF (α : StieltjesFunction ℝ) (ε : ℝ) (hε : 0 ≤ ε) : StieltjesFunction ℝ where
  toFun r := (ε+α r)/(1+ε)
  mono' := by
    intro r s hrs
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith [α.mono hrs]
  right_continuous' := fun r => (continuousWithinAt_const.add (α.right_continuous r)).div_const _

lemma positiveStieltjesCDF_bounds (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 ≤ ε) (r : ℝ) :
    positiveStieltjesCDF α ε hε r ∈ Icc (0:ℝ) 1 := by
  change (ε+α r)/(1+ε) ∈ Icc (0:ℝ) 1
  constructor
  · positivity [(ha r).1]
  · rw [div_le_one (by linarith : 0 < 1+ε)]
    linarith [(ha r).2]

lemma positiveStieltjesCDF_one (α : StieltjesFunction ℝ) (h1 : α 1=1)
    (ε : ℝ) (hε : 0 ≤ ε) : positiveStieltjesCDF α ε hε 1=1 := by
  change (ε+α 1)/(1+ε)=1
  rw [h1]
  field_simp
  ring

lemma positiveStieltjesCDF_pos (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 < ε) (r : ℝ) :
    0 < positiveStieltjesCDF α ε hε.le r := by
  change 0 < (ε+α r)/(1+ε)
  positivity [(ha r).1]

lemma positiveStieltjesCDF_error (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 ≤ ε) (r : ℝ) :
    |positiveStieltjesCDF α ε hε r-α r| ≤ ε := by
  have he : (ε+α r)/(1+ε)-α r=ε*(1-α r)/(1+ε) := by field_simp; ring
  change |(ε+α r)/(1+ε)-α r| ≤ ε
  rw [he,abs_of_nonneg (by positivity [(ha r).2])]
  apply (div_le_iff₀ (by linarith : 0 < 1+ε)).mpr
  nlinarith [(ha r).1,(ha r).2]

lemma scalarCDFGradient_error_of_uniform_coefficient (β : ℝ)
    (α γ : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (hg : ∀ z, γ z ∈ Icc (0:ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ z, |γ z-α z| ≤ ε) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1)
    (η : ℝ) (hη : 0 < η) (x : ℝ) :
    |scalarCDFGradient β γ q (Real.toNNReal (1-q)) x-
      scalarCDFGradient β α q (Real.toNNReal (1-q)) x| ≤
        2*(scalarTimeMassConstant β*ε)/η+2*η := by
  have ht : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [hq.1]
  have hi : (∫ z in q..q+(Real.toNNReal (1-q):ℝ), |γ z-α z|) ≤ ε := by
    have hI : IntervalIntegrable (fun z => |γ z-α z|) volume q
        (q+(Real.toNNReal (1-q):ℝ)) :=
      ((γ.mono.intervalIntegrable.sub α.mono.intervalIntegrable).abs)
    have H := intervalIntegral.integral_mono_on
      (le_add_of_nonneg_right (Real.toNNReal (1-q)).coe_nonneg)
      hI
      (intervalIntegrable_const (c := ε)) (fun z _ => herr z)
    simp only [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul] at H
    exact H.trans (mul_le_of_le_one_left hε (by exact_mod_cast ht))
  have H := scalarCDFGradient_cdf_stability β hg γ.mono ha α.mono q _ ht x η hη
  exact H.trans (by gcongr; exact scalarTimeMassConstant_nonneg β)

lemma finiteTemperatureCDFDrift_error_of_uniform_coefficient (β : ℝ)
    (α γ : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (hg : ∀ z, γ z ∈ Icc (0:ℝ) 1) (h1 : α 1=1) (hg1 : γ 1=1)
    {ε : ℝ} (hε : 0 ≤ ε) (herr : ∀ z, |γ z-α z| ≤ ε)
    (η : ℝ) (hη : 0 < η) (v x : ℝ) :
    |(finiteTemperatureCDFDrift β γ hg hg1).f v x-
      (finiteTemperatureCDFDrift β α ha h1).f v x| ≤
        ε+2*(scalarTimeMassConstant β*ε)/η+2*η := by
  let q := cdfTimeClamp (v/β^2)
  have hq := cdfTimeClamp_mem (v/β^2)
  have ht : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [hq.1]
  have hG := (scalarCDF_derivative_bounds β hg γ.mono q _ ht x).1
  have hD := scalarCDFGradient_error_of_uniform_coefficient β α γ ha hg hε herr hq η hη x
  change |γ q*scalarCDFGradient β γ q (Real.toNNReal (1-q)) x-α q*scalarCDFGradient β α q (Real.toNNReal (1-q)) x| ≤ _
  calc
    _ ≤ |γ q*scalarCDFGradient β γ q (Real.toNNReal (1-q)) x-
        α q*scalarCDFGradient β γ q (Real.toNNReal (1-q)) x|+
      |α q*scalarCDFGradient β γ q (Real.toNNReal (1-q)) x-
        α q*scalarCDFGradient β α q (Real.toNNReal (1-q)) x| := abs_sub_le _ _ _
    _ = |(γ q-α q)*scalarCDFGradient β γ q (Real.toNNReal (1-q)) x|+
      |α q*(scalarCDFGradient β γ q (Real.toNNReal (1-q)) x-scalarCDFGradient β α q (Real.toNNReal (1-q)) x)| := by
      congr 1 <;> congr 1 <;> ring
    _ ≤ ε+(2*(scalarTimeMassConstant β*ε)/η+2*η) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (ha _).1]
      exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) hG).trans (herr q))
        ((mul_le_mul_of_nonneg_left hD (ha _).1).trans
          (mul_le_of_le_one_left (by positivity [scalarTimeMassConstant_nonneg β]) (ha _).2))
    _ = _ := by ring

theorem finiteTemperatureCDFProcess_error_of_uniform_coefficient
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ)
    (α γ : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (hg : ∀ z, γ z ∈ Icc (0:ℝ) 1) (h1 : α 1=1) (hg1 : γ 1=1)
    {ε : ℝ} (hε : 0 ≤ ε) (herr : ∀ z, |γ z-α z| ≤ ε)
    (η : ℝ) (hη : 0 < η) (T v : ℝ≥0) (hv : v ≤ T) (w : Ω) :
    |finiteTemperatureCDFProcess W β γ hg hg1 v w-
      finiteTemperatureCDFProcess W β α ha h1 v w| ≤
        2*(T:ℝ)*(ε+2*(scalarTimeMassConstant β*ε)/η+2*η)*Real.exp (3*(v:ℝ)) := by
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  let a := finiteTemperatureCDFDrift β γ hg hg1
  let b := finiteTemperatureCDFDrift β α ha h1
  let D := ε+2*(scalarTimeMassConstant β*ε)/η+2*η
  have hD : 0 ≤ D := by dsimp [D]; positivity [scalarTimeMassConstant_nonneg β]
  have he : ∀ (Y : ℝ≥0 → Ω → ℝ), IsProgressive ℱ Y → ∀ t ≤ T, ∀ w,
      |timePrimitive (a.action W.driver Y) t w-timePrimitive (b.action W.driver Y) t w| ≤
        (T:ℝ)*D := by
    intro Y hY t ht w
    have H := SKConstants.BoundedLipschitzDrift.primitive_error_of_envelope a b ℱ W.driver Y
      W.driver_progressive hY T (fun _ => D) intervalIntegrable_const
      (fun r _ x => finiteTemperatureCDFDrift_error_of_uniform_coefficient β α γ ha hg h1 hg1
        hε herr η hη r x) t ht w
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at H
    exact H.trans (mul_le_mul_of_nonneg_right ht hD)
  have H := SKConstants.BoundedLipschitzDrift.solution_sub_le_of_primitive_error a b ℱ W.driver
    W.driver_progressive T ((T:ℝ)*D) (mul_nonneg T.coe_nonneg hD) he v hv w
  have hb : b.rate=3 := by norm_num [b,SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.rate,finiteTemperatureCDFDrift]
  rw [hb] at H
  simpa only [a,b,D,finiteTemperatureCDFProcess,mul_assoc] using H

end SKConstants.ParisiFullSupport
