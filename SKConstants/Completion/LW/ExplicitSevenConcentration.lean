module

public import SKConstants.Completion.LW.SevenFamilyProducer
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem correlatedProductVarianceFactor_le_log {R : ℝ} (hR : 1 ≤ R) :
    1 ≤ correlatedProductVarianceFactor R ∧
      correlatedProductVarianceFactor R ≤ 64*Real.log (2+R) := by
  have hR0 : 0 < R := by linarith
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hArg : 1 ≤ 8*Real.exp 1^2*R := by nlinarith
  have hL : 1 ≤ Real.log (2+R) := (Real.le_log_iff_exp_le (by linarith)).mpr
    (Real.exp_one_lt_three.le.trans (by linarith))
  have hlR : Real.log R ≤ Real.log (2+R) := Real.log_le_log hR0 (by linarith)
  have hl2 : Real.log 2 ≤ 1 := (Real.log_le_iff_le_exp (by norm_num)).mpr
    Real.exp_one_gt_two.le
  have hlog : Real.log (8*Real.exp 1^2*R) = 3*Real.log 2+2+Real.log R := by
    rw [Real.log_mul (by positivity) hR0.ne', Real.log_mul (by norm_num) (by positivity),
      show (8 : ℝ)=2^3 by norm_num, Real.log_pow, Real.log_pow, Real.log_exp]
    norm_num
  constructor
  · unfold correlatedProductVarianceFactor
    linarith [Real.log_nonneg hArg]
  · unfold correlatedProductVarianceFactor
    rw [hlog]
    linarith

theorem productVarianceScale_le_sqrt_log {R : ℝ} (hR : 1 ≤ R) :
    productVarianceScale (Real.sqrt R) (correlatedProductVarianceFactor R) ≤
      32*Real.sqrt R*Real.log (2+R) := by
  let F := correlatedProductVarianceFactor R
  let L := Real.log (2+R)
  have hR0 : 0 < R := by linarith
  have hF := correlatedProductVarianceFactor_le_log hR
  have hF0 : 0 < F := by dsimp [F]; linarith [hF.1]
  have hL : 1 ≤ L := (Real.le_log_iff_exp_le (by linarith)).mpr
    (Real.exp_one_lt_three.le.trans (by linarith))
  have hroot : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hLog : Real.log ((4*Real.exp 1*Real.sqrt R)^2/F) ≤ 7*L := by
    have H := Real.log_le_log (by positivity : 0 < (4*Real.exp 1*Real.sqrt R)^2/F)
      (div_le_self (sq_nonneg _) hF.1)
    have heq : Real.log ((4*Real.exp 1*Real.sqrt R)^2) =
        4*Real.log 2+2+Real.log R := by
      rw [Real.log_pow, Real.log_mul (by positivity) (Real.sqrt_pos.mpr hR0).ne',
        Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp,
        show (4 : ℝ)=2^2 by norm_num, Real.log_pow, Real.log_sqrt hR0.le]
      ring
    rw [heq] at H
    have hlR := Real.log_le_log hR0 (by linarith : R ≤ 2+R)
    have hl2 : Real.log 2 ≤ 1 := (Real.log_le_iff_le_exp (by norm_num)).mpr
      Real.exp_one_gt_two.le
    dsimp [L] at *
    linarith
  have hCut : productVarianceCutoff (Real.sqrt R) F ≤ 28*Real.sqrt R*L := by
    unfold productVarianceCutoff
    have H : max 0 (Real.log ((4*Real.exp 1*Real.sqrt R)^2/F)) ≤ 7*L :=
      max_le (by linarith) hLog
    nlinarith [mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ 4*Real.sqrt R)]
  have hSqrt : Real.sqrt F ≤ 8*L := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    have H : L ≤ L^2 := by nlinarith
    nlinarith [hF.2]
  have he3 := Real.exp_one_lt_three
  unfold productVarianceScale
  apply max_le
  · calc
      Real.sqrt F ≤ 8*L := hSqrt
      _ ≤ 32*Real.sqrt R*L := by nlinarith
  · apply max_le
    · nlinarith [mul_le_mul_of_nonneg_right he3.le (Real.sqrt_nonneg R)]
    · exact hCut.trans (by nlinarith)

def explicitSevenVariance (B R : ℝ) (r : ℕ) : ℝ :=
  1024*B^2*(r+1 : ℝ)^2*Real.log (2+R)

def explicitSevenRadius (B R : ℝ) (r : ℕ) : ℝ :=
  1/(128*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R))

theorem weightedProducer_le_explicit {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R) (r : ℕ) :
    weightedProducerVariance B R r ≤ explicitSevenVariance B R r ∧
      explicitSevenRadius B R r ≤ weightedProducerRadius B R r := by
  have hR0 : 0 < R := by linarith
  have hL : 0 < Real.log (2+R) := Real.log_pos (by linarith)
  have hF := correlatedProductVarianceFactor_le_log hR
  have hS := productVarianceScale_le_sqrt_log hR
  have hS0 := productVarianceScale_pos (s := correlatedProductVarianceFactor R)
    (Real.sqrt_pos.mpr hR0)
  constructor
  · unfold weightedProducerVariance productMGFVariance explicitSevenVariance
    nlinarith [mul_le_mul_of_nonneg_left hF.2 (by positivity : 0 ≤ 16*(B*(r+1 : ℝ))^2)]
  · unfold explicitSevenRadius weightedProducerRadius productMGFRadius
    rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hS (by positivity : 0 ≤ 4*(B*(r+1 : ℝ)))]

theorem actual_seven_duration_tail_explicit
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ) (hV : t (2^r+1) ≤ V)
    {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hRatio : ∀ j : Fin (2^r), previousDuration t (j+1)/previousDuration t j ≤ B^2)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    (linkedScalarRowsLaw W Z β V n).real
      {ω | 4*η^2*(2+5*(r+1 : ℝ)*∑ j : Fin (2^r), previousDuration t j) <
        ∑ i : SevenIndex r, ‖rowAverage (sevenRow W Z β hβ t V r i) ω‖^2} ≤
      2*(10*(2 : ℝ)^r-3)*(5 : ℝ)^(2^r)*Real.exp (-(n : ℝ)*
        min (η^2/(4096*B^2*(r+1 : ℝ)^2*Real.log (2+R)))
          (η/(256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R)))) := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hL : 0 < Real.log (2+R) := Real.log_pos (by linarith)
  have hp := weightedProducer_le_explicit hB0 hR r
  have hRows := actualSevenRowMGF_of_adjacent_ratio W Z β hβ t ht V r hV hB hR hProxy hRatio
  have hRows' : ActualSevenRowMGFStatement W Z β hβ t V r
      (explicitSevenVariance B R r) (explicitSevenRadius B R r) :=
    fun i a ha => localMGF_mono (hRows i a ha) hp.1 hp.2
  have H := actual_seven_duration_total_tail W Z β hβ t ht V r hn
    (by unfold explicitSevenVariance; positivity) (by unfold explicitSevenRadius; positivity) hη hRows'
  convert H using 1 <;> unfold explicitSevenVariance explicitSevenRadius <;> congr 4 <;> field_simp <;> ring

theorem actual_seven_simultaneous_tail_explicit
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ) (hV : t (2^r+1) ≤ V)
    {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hRatio : ∀ j : Fin (2^r), previousDuration t (j+1)/previousDuration t j ≤ B^2)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    (linkedScalarRowsLaw W Z β V n).real
      {ω | ∃ i : SevenIndex r,
        2*η*Real.sqrt (sevenDuration r (fun j => previousDuration t j) i) <
          ‖rowAverage (sevenRow W Z β hβ t V r i) ω‖} ≤
      2*(10*(2 : ℝ)^r-3)*(5 : ℝ)^(2^r)*Real.exp (-(n : ℝ)*
        min (η^2/(4096*B^2*(r+1 : ℝ)^2*Real.log (2+R)))
          (η/(256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R)))) := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hL : 0 < Real.log (2+R) := Real.log_pos (by linarith)
  have hp := weightedProducer_le_explicit hB0 hR r
  have hRows := actualSevenRowMGF_of_adjacent_ratio W Z β hβ t ht V r hV hB hR hProxy hRatio
  have hRows' : ActualSevenRowMGFStatement W Z β hβ t V r
      (explicitSevenVariance B R r) (explicitSevenRadius B R r) :=
    fun i a ha => localMGF_mono (hRows i a ha) hp.1 hp.2
  have hd (i : SevenIndex r) : 0 < sevenDuration r (fun j => previousDuration t j) i := by
    cases i with
    | inl _ => exact zero_lt_one
    | inr p =>
      exact Finset.sum_pos
        (fun j _ => sub_pos.mpr (NNReal.coe_lt_coe.mpr (ht (Nat.lt_succ_self _))))
        (dyadicIntervalSets_nonempty r p.2)
  have H := iid_duration_family_tail (linkedScalarLaw W Z β V) hn
    (sevenRow W Z β hβ t V r) (measurable_sevenRow W Z β hβ t V r)
    (sevenDuration r (fun j => previousDuration t j)) (fun i => (hd i).le)
    (fun i hi => False.elim ((hd i).ne' hi))
    (by unfold explicitSevenVariance; positivity) (by unfold explicitSevenRadius; positivity) hη hRows'
  rw [card_SevenIndex] at H
  convert H using 1
  · rfl
  · unfold explicitSevenVariance explicitSevenRadius
    congr 4 <;> field_simp <;> ring

end SKConstants.Completion.LW
