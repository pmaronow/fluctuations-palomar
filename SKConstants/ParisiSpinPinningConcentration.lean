module
public import SKConstants.ParisiSpinPinning
public import SKConstants.BoundedPinningBernstein
public import SKConstants.ScalarProcessRowMGFVariance

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiSpinPinningConcentration_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem actualParisiPinningError_mean_postProfile
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (v T : ℝ≥0)
    (hST : parisiEquilibriumPhysicalEndpoint β+v≤T) :
    (∫ u,actualParisiPinningError W β (parisiEquilibriumPhysicalEndpoint β+v) u
      ∂actualParisiFullTerminalSpinLaw β W T) = actualParisiContinuationP W β v := by
  let S := parisiEquilibriumPhysicalEndpoint β+v
  rw [actualParisiPinningError_mean W β hβ S T hST,
    actualParisiContinuationP_eq_full_process_moment W β hβ v v.coe_nonneg]
  simp only [Real.toNNReal_coe]
  have hs : β^2*parisiEquilibriumSupportEndpoint β ≤ (S:ℝ) := by
    dsimp [S]
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
    exact le_add_of_nonneg_right v.coe_nonneg
  have hm (w : Ω) : actualParisiFullPosteriorMean W β S w =
      Real.tanh (actualParisiFullScalarProcess W β S w) := by
    unfold actualParisiFullPosteriorMean
    rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ S hs]
  have hi : Integrable (fun w => (actualParisiFullPosteriorMean W β S w)^2) W.law := by
    apply Integrable.of_bound (f := fun w => (actualParisiFullPosteriorMean W β S w)^2)
      ((measurable_actualParisiFullPosteriorMean W β S).pow_const 2).aestronglyMeasurable 1
    exact ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs,abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (abs_actualParisiFullPosteriorMean_le W β S w) 2).trans_eq
        (by norm_num))
  calc
    1-(∫ w,(actualParisiFullPosteriorMean W β S w)^2 ∂W.law) =
        ∫ w,1-(actualParisiFullPosteriorMean W β S w)^2 ∂W.law := by
      rw [integral_sub (f := fun _ : Ω => (1:ℝ)) (g := fun w => (actualParisiFullPosteriorMean W β S w)^2)
        (integrable_const 1) hi]
      simp
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun w => by
        change 1-(actualParisiFullPosteriorMean W β S w)^2 =
          scalarDefect (actualParisiFullScalarProcess W β S w)
        rw [hm]
        rfl)

def actualParisiTerminalSpinRowsLaw (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) (n : ℕ) :
    Measure (Fin n → Bool × Ω) :=
  Measure.pi (fun _ : Fin n => actualParisiFullTerminalSpinLaw β W T)

instance actualParisiTerminalSpinRowsLaw_isProbability (W : BrownianSystem Ω) (β : ℝ)
    (T : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (actualParisiTerminalSpinRowsLaw W β T n) := by
  unfold actualParisiTerminalSpinRowsLaw
  infer_instance

theorem actualParisiPinning_iid_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (v T : ℝ≥0) (hv : 0<v) (hST : parisiEquilibriumPhysicalEndpoint β+v≤T)
    (n : ℕ) (hn : 0<n) (η : ℝ) (hη : 0<η) (hSmall : 8*scalarTailScale v≤η) :
    (actualParisiTerminalSpinRowsLaw W β T n).real
      {ω | 2*η≤(∑ i : Fin n,actualParisiPinningError W β
        (parisiEquilibriumPhysicalEndpoint β+v) (ω i))/(n:ℝ)} ≤
      2*Real.exp (-(n:ℝ)*η/8) := by
  apply Concentration.bounded_pinning_iid_tail _ _
    (measurable_actualParisiPinningError W β _) (actualParisiPinningError_mem_Icc W β _)
    n hn (4*scalarTailScale v) η (mul_pos (by norm_num) (scalarTailScale_pos hv)) hη _
    (by linarith)
  rw [actualParisiPinningError_mean_postProfile W β hβ v T hST]
  simpa only [Real.toNNReal_coe] using actualParisiContinuationP_le_tail W β v
    (by exact_mod_cast hv)

lemma scalarTailScale_le_exp_of_one_le (v : ℝ≥0) (hv : 1≤v) :
    scalarTailScale v≤Real.exp (-(v:ℝ)/2) := by
  have hvR : (1:ℝ)≤(v:ℝ) := by exact_mod_cast hv
  have hprod : (1:ℝ)≤2*Real.pi*(v:ℝ) := by
    nlinarith [Real.pi_gt_three]
  have hden : (1:ℝ)≤Real.sqrt (2*Real.pi*(v:ℝ)) := Real.one_le_sqrt.mpr hprod
  unfold scalarTailScale
  norm_num only [Nat.cast_ofNat]
  exact (mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hden) (Real.exp_pos _).le).trans_eq
    (by rw [mul_one])

theorem actualParisiPinning_iid_tail_exp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (v T : ℝ≥0) (hv : 1≤v) (hST : parisiEquilibriumPhysicalEndpoint β+v≤T)
    (n : ℕ) (hn : 0<n) (η : ℝ) (hη : 0<η) (hSmall : 8*Real.exp (-(v:ℝ)/2)≤η) :
    (actualParisiTerminalSpinRowsLaw W β T n).real
      {ω | 2*η≤(∑ i : Fin n,actualParisiPinningError W β
        (parisiEquilibriumPhysicalEndpoint β+v) (ω i))/(n:ℝ)} ≤
      2*Real.exp (-(n:ℝ)*η/8) :=
  actualParisiPinning_iid_tail W β hβ v T (lt_of_lt_of_le (by norm_num) hv) hST
    n hn η hη ((mul_le_mul_of_nonneg_left (scalarTailScale_le_exp_of_one_le v hv)
      (by norm_num)).trans hSmall)

end SKConstants
