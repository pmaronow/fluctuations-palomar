module

public import SKConstants.ScalarProcessMixedRowPrimitives
public import Mathlib.Data.Fin.Tuple.Reflection

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {d n : ℕ}

def scalarMixedPosteriorInnovationRow (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) (u : Bool × Ω) :
    EuclideanSpace ℝ (Fin (d + (d+1))) :=
  WithLp.toLp 2 (Fin.append
    (scalarNormalizedPosteriorRow z B t s u).ofLp
    (Fin.append (scalarNormalizedInnovationRow z B q u).ofLp
      (fun _ : Fin 1 => scalarHiddenSign u.1 - Real.tanh z)))

def mixedPosteriorCoefficient (a : EuclideanSpace ℝ (Fin (d+(d+1)))) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => a (Fin.castAdd (d+1) i))

def mixedInnovationCoefficient (a : EuclideanSpace ℝ (Fin (d+(d+1)))) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => a (Fin.natAdd d (Fin.castAdd 1 i)))

def mixedSpinCoefficient (a : EuclideanSpace ℝ (Fin (d+(d+1)))) : ℝ :=
  a (Fin.natAdd d (Fin.natAdd d (0 : Fin 1)))

theorem mixedCoefficient_norm_sq (a : EuclideanSpace ℝ (Fin (d+(d+1)))) :
    ‖a‖^2 = ‖mixedPosteriorCoefficient a‖^2 + ‖mixedInnovationCoefficient a‖^2 +
      (mixedSpinCoefficient a)^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add,
    mixedPosteriorCoefficient, mixedInnovationCoefficient, mixedSpinCoefficient,
    WithLp.ofLp_toLp, Fin.sum_univ_one]
  ring

theorem scalarMixedPosteriorInnovationRow_inner (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) (u : Bool × Ω)
    (a : EuclideanSpace ℝ (Fin (d+(d+1)))) :
    ⟪scalarMixedPosteriorInnovationRow z B t q s u, a⟫_ℝ =
      ⟪scalarNormalizedPosteriorRow z B t s u, mixedPosteriorCoefficient a⟫_ℝ +
      ⟪scalarNormalizedInnovationRow z B q u, mixedInnovationCoefficient a⟫_ℝ +
      mixedSpinCoefficient a * (scalarHiddenSign u.1 - Real.tanh z) := by
  simp only [scalarMixedPosteriorInnovationRow, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, WithLp.ofLp_toLp, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, mixedPosteriorCoefficient,
    mixedInnovationCoefficient, mixedSpinCoefficient, Fin.sum_univ_one]
  ring

theorem measurable_scalarMixedPosteriorInnovationRow (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (Function.uncurry B)) (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) :
    Measurable (scalarMixedPosteriorInnovationRow z B t q s) := by
  have hT := measurable_scalarNormalizedPosteriorRow z B
    (fun T => hBm.comp (measurable_const.prodMk measurable_id)) t s
  have hG := measurable_scalarNormalizedInnovationRow (d := d) z B hBm q
  have hS : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1 - Real.tanh z) :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub_const (Real.tanh z)
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [scalarMixedPosteriorInnovationRow, Fin.append_left, Function.comp_def] using
      (measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 _).comp hT)
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) j
    · simpa only [Fin.append_right, Fin.append_left, Function.comp_def] using
        (measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 _).comp hG)
    · simpa only [Fin.append_right] using hS

private theorem subGaussian_proxy_enlarge {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {X : A → ℝ} {K L : ℝ≥0}
    (h : HasSubgaussianMGF X K μ) (hKL : K ≤ L) : HasSubgaussianMGF X L μ := by
  refine ⟨h.integrable_exp_mul, fun θ => (h.mgf_le θ).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hKL) (sq_nonneg θ)) (by norm_num)

private theorem sqrt_sum_sq_le (K L : ℝ≥0) : (K.sqrt+L.sqrt)^2 ≤ 2*(K+L) := by
  apply NNReal.coe_le_coe.mp
  push_cast
  nlinarith [Real.sq_sqrt K.coe_nonneg, Real.sq_sqrt L.coe_nonneg,
    sq_nonneg (Real.sqrt (K : ℝ) - Real.sqrt (L : ℝ))]

theorem scalarMixedPosteriorInnovationRow_unit_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t q : ℕ → ℝ≥0) (ht : Monotone t) (hq : StrictMono q)
    (s : Fin d → ℝ≥0) (hs : ∀ i, 0 < s i) (K : ℝ≥0)
    (hbudget : ∀ i : Fin d, t (i+1)-t i ≤ K*s i^2)
    (a : EuclideanSpace ℝ (Fin (d+(d+1)))) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪scalarMixedPosteriorInnovationRow z B t q s u, a⟫_ℝ)
      (4*K+8) (scalarHiddenBrownianLaw z P) := by
  have hn := mixedCoefficient_norm_sq a
  have ha2 : ‖a‖^2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hTnorm : ‖mixedPosteriorCoefficient a‖ ≤ 1 := by
    nlinarith [sq_nonneg (mixedSpinCoefficient a), sq_nonneg ‖mixedInnovationCoefficient a‖,
      norm_nonneg (mixedPosteriorCoefficient a)]
  have hGnorm : ‖mixedInnovationCoefficient a‖ ≤ 1 := by
    nlinarith [sq_nonneg (mixedSpinCoefficient a), sq_nonneg ‖mixedPosteriorCoefficient a‖,
      norm_nonneg (mixedInnovationCoefficient a)]
  have hSnorm : (mixedSpinCoefficient a)^2 ≤ 1 := by
    nlinarith [sq_nonneg ‖mixedPosteriorCoefficient a‖, sq_nonneg ‖mixedInnovationCoefficient a‖]
  have hT := scalarNormalizedPosteriorRow_unit_hasSubgaussianMGF P z B hB t ht s hs K
    hbudget (mixedPosteriorCoefficient a) hTnorm
  have hG := scalarNormalizedInnovationRow_unit_hasSubgaussianMGF P z B hB q hq
    (mixedInnovationCoefficient a) hGnorm
  have hS : HasSubgaussianMGF
      (fun u : Bool × Ω => mixedSpinCoefficient a*(scalarHiddenSign u.1 - Real.tanh z)) 1
      (scalarHiddenBrownianLaw z P) := by
    apply subGaussian_proxy_enlarge ((scalarHiddenCenteredSign_hasSubgaussianMGF P z).const_mul _)
    apply NNReal.coe_le_coe.mp
    change (mixedSpinCoefficient a)^2*1 ≤ (1 : ℝ)
    simpa only [mul_one] using hSnorm
  have hTG := subGaussian_proxy_enlarge (hT.add hG) (sqrt_sum_sq_le K 1)
  have hAll := subGaussian_proxy_enlarge (hTG.add hS) (sqrt_sum_sq_le (2*(K+1)) 1)
  have hFinal := subGaussian_proxy_enlarge hAll (show 2*(2*(K+1)+1) ≤ 4*K+8 by
    apply NNReal.coe_le_coe.mp; push_cast; linarith)
  simpa only [scalarMixedPosteriorInnovationRow_inner] using hFinal

theorem scalarActualMixedPosteriorInnovationRow_secondMoment_le
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t q : ℕ → ℝ≥0) (ht : StrictMono t) (hq : StrictMono q) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V)
    (a : EuclideanSpace ℝ (Fin (d+(d+1)))) :
    (∫ u, ⟪scalarMixedPosteriorInnovationRow z B t q
      (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u, a⟫_ℝ ^ 2
      ∂scalarHiddenBrownianLaw z P) ≤ 3*‖a‖^2 := by
  let s : Fin d → ℝ≥0 := fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))
  let T : Bool × Ω → ℝ := fun u => ⟪scalarNormalizedPosteriorRow z B t s u,
    mixedPosteriorCoefficient a⟫_ℝ
  let G : Bool × Ω → ℝ := fun u => ⟪scalarNormalizedInnovationRow z B q u,
    mixedInnovationCoefficient a⟫_ℝ
  let S : Bool × Ω → ℝ := fun u => mixedSpinCoefficient a*(scalarHiddenSign u.1 - Real.tanh z)
  have hT := scalarNormalizedPosteriorRow_linearForm_hasSubgaussianMGF P z B hB t ht.monotone s
    (mixedPosteriorCoefficient a)
  have hG := scalarNormalizedInnovationRow_linearForm_hasSubgaussianMGF P z B hB q hq
    (mixedInnovationCoefficient a)
  have hS := (scalarHiddenCenteredSign_hasSubgaussianMGF P z).const_mul (mixedSpinCoefficient a)
  have hTint : Integrable (fun u => T u^2) (scalarHiddenBrownianLaw z P) :=
    (hT.memLp 2).integrable_sq
  have hGint : Integrable (fun u => G u^2) (scalarHiddenBrownianLaw z P) :=
    (hG.memLp 2).integrable_sq
  have hSint : Integrable (fun u => S u^2) (scalarHiddenBrownianLaw z P) :=
    (hS.memLp 2).integrable_sq
  have hTE : (∫ u, T u^2 ∂scalarHiddenBrownianLaw z P) = ‖mixedPosteriorCoefficient a‖^2 :=
    scalarActualNormalizedPosteriorRow_secondMoment P z B hB R hR hz t ht V ht1 htV _
  have hGE : (∫ u, G u^2 ∂scalarHiddenBrownianLaw z P) = ‖mixedInnovationCoefficient a‖^2 :=
    scalarNormalizedInnovationRow_linearForm_secondMoment P z B hB q hq _
  have hSE : (∫ u, S u^2 ∂scalarHiddenBrownianLaw z P) ≤ (mixedSpinCoefficient a)^2 := by
    have he : (fun u => S u^2) = fun u => (mixedSpinCoefficient a)^2*
        (scalarHiddenSign u.1 - Real.tanh z)^2 := by ext u; dsimp [S]; ring
    rw [he, integral_const_mul, scalarHiddenCenteredSign_secondMoment]
    nlinarith [sq_nonneg (mixedSpinCoefficient a * Real.tanh z)]
  have hPoint (u : Bool × Ω) : (T u+G u+S u)^2 ≤ 3*(T u^2+G u^2+S u^2) := by
    nlinarith [sq_nonneg (T u-G u), sq_nonneg (T u-S u), sq_nonneg (G u-S u)]
  calc
    _ = ∫ u, (T u+G u+S u)^2 ∂scalarHiddenBrownianLaw z P := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => congrArg (fun x : ℝ => x^2)
        (scalarMixedPosteriorInnovationRow_inner z B t q s u a))
    _ ≤ ∫ u, 3*(T u^2+G u^2+S u^2) ∂scalarHiddenBrownianLaw z P :=
      integral_mono_of_nonneg (ae_of_all _ (fun u => sq_nonneg _))
        ((hTint.add hGint).add hSint |>.const_mul 3) (ae_of_all _ hPoint)
    _ = 3*((∫ u, T u^2 ∂scalarHiddenBrownianLaw z P) +
        (∫ u, G u^2 ∂scalarHiddenBrownianLaw z P) +
        (∫ u, S u^2 ∂scalarHiddenBrownianLaw z P)) := by
      rw [integral_const_mul]
      have hsum := integral_add (hTint.add hGint) hSint
      have hsum2 := integral_add hTint hGint
      simp only [Pi.add_apply] at hsum hsum2
      rw [hsum, hsum2]
    _ ≤ 3*(‖mixedPosteriorCoefficient a‖^2+‖mixedInnovationCoefficient a‖^2+
        (mixedSpinCoefficient a)^2) := by rw [hTE, hGE]; linarith
    _ = _ := by rw [← mixedCoefficient_norm_sq]

end SKConstants

namespace SKConstants

variable {Ω : Type*} [MeasurableSpace Ω] {d n : ℕ}

def scalarMixedPosteriorInnovationRows (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) (i : Fin n) (ω : Fin n → Bool × Ω) :
    EuclideanSpace ℝ (Fin (d+(d+1))) :=
  scalarMixedPosteriorInnovationRow z B t q s (ω i)

theorem measurable_scalarMixedPosteriorInnovationRows
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hBm : Measurable (Function.uncurry B))
    (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) (i : Fin n) :
    Measurable (scalarMixedPosteriorInnovationRows z B t q s i) :=
  (measurable_scalarMixedPosteriorInnovationRow z B hBm t q s).comp (measurable_pi_apply i)

theorem scalarMixedPosteriorInnovationRows_independent
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hBm : Measurable (Function.uncurry B))
    (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0) :
    iIndepFun (scalarMixedPosteriorInnovationRows (n := n) z B t q s)
      (scalarPosteriorRowsLaw P z n) := by
  exact iIndepFun_pi (μ := fun _ : Fin n => scalarHiddenBrownianLaw z P)
    (X := fun _ : Fin n => scalarMixedPosteriorInnovationRow z B t q s)
    (fun _ => (measurable_scalarMixedPosteriorInnovationRow z B hBm t q s).aemeasurable)

private theorem mixed_hasSubgaussianMGF_product_copy {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ) (K : ℝ≥0)
    (hF : HasSubgaussianMGF F K μ) (i : Fin n) :
    HasSubgaussianMGF (fun ω : Fin n → A => F (ω i)) K
      (Measure.pi (fun _ : Fin n => μ)) := by
  apply HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq]
  exact hF

private theorem mixed_integral_product_copy {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ)
    (hF : AEStronglyMeasurable F μ) (i : Fin n) :
    (∫ ω : Fin n → A, F (ω i) ∂Measure.pi (fun _ : Fin n => μ)) = ∫ u, F u ∂μ := by
  have heval := (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
  have hMap : AEStronglyMeasurable F
      ((Measure.pi (fun _ : Fin n => μ)).map (Function.eval i)) := by
    rwa [heval]
  rw [← integral_map (measurable_pi_apply i).aemeasurable hMap, heval]

def scalarMixedRowMGFProxy (R : ℝ) (V : ℝ≥0) : ℝ≥0 :=
  4*scalarPosteriorRowMGFProxy R V+8

theorem scalarPosteriorRowMGFProxy_eq (R : ℝ) (V : ℝ≥0) :
    (scalarPosteriorRowMGFProxy R V : ℝ) =
      (scalarCompactTailConstant R)⁻¹ * Real.sqrt (2*Real.pi*(V : ℝ)) *
        Real.exp ((V : ℝ)/2) := by
  rw [scalarPosteriorRowMGFProxy, NNReal.coe_inv,
    Real.coe_toNNReal _ (mul_nonneg (scalarCompactTailConstant_pos R).le (scalarTailScale_nonneg V))]
  unfold scalarTailScale
  norm_num only [Nat.cast_ofNat]
  rw [neg_div, Real.exp_neg]
  simp only [mul_inv_rev, inv_inv]
  ring

theorem scalarActualMixedPosteriorInnovationRows_covariance_operator_variance_tail
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t q : ℕ → ℝ≥0) (ht : StrictMono t) (hq : StrictMono q) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V)
    (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    (scalarPosteriorRowsLaw P z n).real
      {ω | 2*η < ‖Concentration.centeredEmpiricalCovariance (scalarPosteriorRowsLaw P z n)
        (scalarMixedPosteriorInnovationRows z B t q
          (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1)))) ω‖} ≤
      2*(9 : ℝ)^(d+(d+1))*Real.exp (-(n : ℝ)*min
        (η^2/(192*Concentration.squareVarianceScale (scalarMixedRowMGFProxy R V : ℝ) 3))
        (η/(8*Concentration.squareVarianceScale (scalarMixedRowMGFProxy R V : ℝ) 3))) := by
  let s : Fin d → ℝ≥0 := fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))
  have hSi (i : Fin d) : 1 ≤ (t i : ℝ) :=
    ht1.trans (NNReal.coe_le_coe.mpr (ht.monotone (Nat.zero_le _)))
  have hTi (i : Fin d) : t (i+1) ≤ V := (ht.monotone (by omega)).trans htV
  have hs (i : Fin d) : 0 < s i := scalarPosteriorIntervalScale_pos P z B hB R hR hz
    (t i) (t (i+1)) V (hSi i) (ht (Nat.lt_succ_self _)) (hTi i)
  have hbudget (i : Fin d) : t (i+1)-t i ≤ scalarPosteriorRowMGFProxy R V*s i^2 :=
    scalarPosteriorIntervalScale_budget P z B hB R hR hz (t i) (t (i+1)) V
      (hSi i) (ht.monotone (Nat.le_succ _)) (hTi i)
  have hMGF (i : Fin n) (a : EuclideanSpace ℝ (Fin (d+(d+1)))) (ha : ‖a‖ ≤ 1) :
      HasSubgaussianMGF (fun ω => ⟪scalarMixedPosteriorInnovationRows z B t q s i ω,a⟫_ℝ)
        (scalarMixedRowMGFProxy R V) (scalarPosteriorRowsLaw P z n) := by
    simpa only [scalarMixedPosteriorInnovationRows, scalarPosteriorRowsLaw] using
      mixed_hasSubgaussianMGF_product_copy (scalarHiddenBrownianLaw z P)
        (fun u => ⟪scalarMixedPosteriorInnovationRow z B t q s u,a⟫_ℝ)
        (scalarMixedRowMGFProxy R V)
        (scalarMixedPosteriorInnovationRow_unit_hasSubgaussianMGF P z B hB t q ht.monotone hq
          s hs (scalarPosteriorRowMGFProxy R V) hbudget a ha) i
  have hSecond (i : Fin n) (a : EuclideanSpace ℝ (Fin (d+(d+1)))) (ha : ‖a‖ ≤ 1) :
      (∫ ω, ⟪scalarMixedPosteriorInnovationRows z B t q s i ω,a⟫_ℝ^2
        ∂scalarPosteriorRowsLaw P z n) ≤ 3 := by
    have hF : Measurable (fun u => ⟪scalarMixedPosteriorInnovationRow z B t q s u,a⟫_ℝ^2) := by
      have hm := measurable_scalarMixedPosteriorInnovationRow z B hBm t q s
      fun_prop
    have he : (∫ ω, ⟪scalarMixedPosteriorInnovationRows z B t q s i ω,a⟫_ℝ^2
        ∂scalarPosteriorRowsLaw P z n) =
        ∫ u, ⟪scalarMixedPosteriorInnovationRow z B t q s u,a⟫_ℝ^2
          ∂scalarHiddenBrownianLaw z P := by
      simpa only [scalarMixedPosteriorInnovationRows, scalarPosteriorRowsLaw] using
        mixed_integral_product_copy (scalarHiddenBrownianLaw z P)
          (fun u => ⟪scalarMixedPosteriorInnovationRow z B t q s u,a⟫_ℝ^2)
          hF.aestronglyMeasurable i
    rw [he]
    have hbound := scalarActualMixedPosteriorInnovationRow_secondMoment_le P z B hB R hR hz
      t q ht hq V ht1 htV a
    have ha2 : ‖a‖^2 ≤ 1 := by nlinarith [norm_nonneg a]
    exact hbound.trans (by nlinarith)
  simpa only [show (64 : ℝ)*3=192 by norm_num] using
    Concentration.independent_empirical_covariance_operator_variance_tail hn
      (scalarMixedPosteriorInnovationRows z B t q s)
      (scalarMixedPosteriorInnovationRows_independent P z B hBm t q s)
      (measurable_scalarMixedPosteriorInnovationRows z B hBm t q s)
      (scalarMixedRowMGFProxy R V) (by dsimp [scalarMixedRowMGFProxy]; positivity)
      hMGF 3 (by norm_num) hSecond η hη

end SKConstants
