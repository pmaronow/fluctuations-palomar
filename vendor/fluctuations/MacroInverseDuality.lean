module

public import MacroQuantileCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Measure.Subtype.measureSpace

theorem macroForwardProfile_cdf_eq_inverse {ζ L : ℝ} (hζ : 0 < ζ) (hL : 1 < L)
    (A : MacroInverseClass ζ L) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    (quantileMassProfile A.val.val (fun u _ => A.val.property.1 u)).val r =
      macroInverseQuantile hζ hL A r := by
  rw [quantileMassProfile_cdf _ (A.val.property.2.monotoneOn _)]
  have hq := macroInverseQuantile_bounds hζ hL A r
  have hs := inverseConstraint_strictMonoOn hζ continuousOn_const (fun _ _ => le_rfl) A.property
  have hspec := macroInverseQuantile_spec hζ hL A hr
  have he : {u : ParisiFinite.OrderPoint | A.val.val u ≤ r} =
      {u : ParisiFinite.OrderPoint | (u:ℝ) ≤ macroInverseQuantile hζ hL A r} := by
    ext u
    constructor
    · intro hu
      exact hs.le_iff_le u.property hq |>.mp (by rwa [hspec])
    · intro hu
      exact (A.val.property.2 hu).trans_eq hspec
  rw [he,uniformOrderMass_atMost hq]

theorem macroForwardProfile_inverse_bounds {ζ L : ℝ} (hζ : 0 < ζ) (hL : 1 < L)
    (A : MacroInverseClass ζ L) {r s : ℝ} (hr : r ∈ Icc (0:ℝ) 1)
    (hs : s ∈ Icc (0:ℝ) 1) (hrs : r ≤ s) :
    (1/L)*(s-r) ≤ macroInverseQuantile hζ hL A s-macroInverseQuantile hζ hL A r ∧
    macroInverseQuantile hζ hL A s-macroInverseQuantile hζ hL A r ≤ (1/ζ)*(s-r) := by
  let q := macroInverseQuantile hζ hL A
  have hqr := macroInverseQuantile_bounds hζ hL A r
  have hqs := macroInverseQuantile_bounds hζ hL A s
  have hqrs := macroInverseQuantile_monotone hζ hL A hr hs hrs
  have hgap := A.property.2.2 (q r) hqr (q s) hqs hqrs
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hgap
  rw [macroInverseQuantile_spec hζ hL A hr,macroInverseQuantile_spec hζ hL A hs] at hgap
  constructor
  · rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (zero_lt_one.trans hL)).mpr
    exact hgap.2
  · rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hζ).mpr
    exact hgap.1

def macroInverseDual {ζ L η Q : ℝ} (hζ : 0 < ζ) (hL : 1 < L)
    (A : MacroInverseClass ζ L) (hη : η ≤ 1/L) (hQ : 1/ζ ≤ Q) :
    MacroInverseClass η Q :=
  ⟨quantileMassProfile A.val.val (fun u _ => A.val.property.1 u),by
    have hq0 : macroInverseQuantile hζ hL A 0=0 := by
      simpa only [A.property.1] using macroInverseQuantile_inverse hζ hL A 0 (by norm_num)
    have hq1 : macroInverseQuantile hζ hL A 1=1 := by
      simpa only [A.property.2.1] using macroInverseQuantile_inverse hζ hL A 1 (by norm_num)
    refine ⟨?_,?_,?_⟩
    · rw [macroForwardProfile_cdf_eq_inverse hζ hL A (by norm_num),hq0]
    · rw [macroForwardProfile_cdf_eq_inverse hζ hL A (by norm_num),hq1]
    · intro r hr s hs hrs
      rw [macroForwardProfile_cdf_eq_inverse hζ hL A hr,macroForwardProfile_cdf_eq_inverse hζ hL A hs]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      have hgap := macroForwardProfile_inverse_bounds hζ hL A hr hs hrs
      exact ⟨by nlinarith [mul_le_mul_of_nonneg_right hη (sub_nonneg.mpr hrs)],
        by nlinarith [mul_le_mul_of_nonneg_right hQ (sub_nonneg.mpr hrs)]⟩⟩

theorem macroInverseDual_quantile {ζ L η Q : ℝ} (hζ : 0 < ζ) (hL : 1 < L)
    (A : MacroInverseClass ζ L) (hη : η ≤ 1/L) (hQ : 1/ζ ≤ Q)
    (hη0 : 0 < η) (hQ1 : 1 < Q) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    macroInverseQuantile hη0 hQ1 (macroInverseDual hζ hL A hη hQ) u = A.val.val u := by
  have hAu := A.val.property.1 u
  have hid : (macroInverseDual hζ hL A hη hQ).val.val (A.val.val u)=u := by
    change (quantileMassProfile A.val.val (fun u _ => A.val.property.1 u)).val (A.val.val u)=u
    rw [macroForwardProfile_cdf_eq_inverse hζ hL A hAu,macroInverseQuantile_inverse hζ hL A u hu]
  have hi := macroInverseQuantile_inverse hη0 hQ1 (macroInverseDual hζ hL A hη hQ) (A.val.val u) hAu
  rwa [hid] at hi

end OAI.SKFluctuations.LaplaceWindowFormalization
