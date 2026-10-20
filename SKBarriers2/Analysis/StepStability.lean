module

public import SKBarriers2.Analysis.StepExpansion
public import SKBarriers2.Analysis.GaussianJets

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
open OAI.SK.Analytic

namespace SKBarriers2

theorem QPotential.mono {r : ℕ} {B C : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential r B f) (hBC : B ≤ C) : QPotential r C f := by
  exact ⟨hf.nonneg.trans hBC, hf.smooth, fun j hj hjr x => (hf.bound j hj hjr x).trans hBC⟩

theorem QPotential.derivativeJets {r : ℕ} {B : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential (r + 1) B f) : QBoundedJets r B (fderiv ℝ f) := by
  refine ⟨hf.nonneg, hf.smooth.fderiv_right (by simp), ?_⟩
  intro j hj x
  rw [norm_iteratedFDeriv_fderiv]
  exact hf.bound (j + 1) (by omega) (by omega) x

namespace QBoundedJets

variable {X Y Z W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem bilinear {r : ℕ} {B C : ℝ} {f : X → Y} {g : X → Z}
    (hf : QBoundedJets r B f) (hg : QBoundedJets r C g)
    (L : Y →L[ℝ] Z →L[ℝ] W) (hL : ‖L‖ ≤ 1) :
    QBoundedJets r ((2 : ℝ) ^ r * B * C) (fun x => L (f x) (g x)) := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  refine ⟨by positivity, (L.contDiff.comp hf.smooth).clm_apply hg.smooth, ?_⟩
  intro j hj x
  calc
    ‖iteratedFDeriv ℝ j (fun x => L (f x) (g x)) x‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      L.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf.smooth hg.smooth x (by exact_mod_cast hj) hL
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      gcongr
      · exact hf.bound i (hi'.trans hj) x
      · exact hg.bound (j - i) (by omega) x
    _ = (2 : ℝ) ^ j * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 : ℝ) ^ r * B * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hB) hC

theorem smulRight {r : ℕ} {B C : ℝ} {f : X → Y →L[ℝ] ℝ} {g : X → Z}
    (hf : QBoundedJets r B f) (hg : QBoundedJets r C g) :
    QBoundedJets r ((2 : ℝ) ^ r * B * C) (fun x => (f x).smulRight (g x)) := by
  apply hf.bilinear hg (ContinuousLinearMap.smulRightL ℝ Y Z)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro b
  change ‖a.smulRight b‖ ≤ ‖a‖ * ‖b‖
  exact (ContinuousLinearMap.norm_smulRight_apply a b).le

theorem apply_const {r : ℕ} {B : ℝ} {f : X → Y →L[ℝ] Z}
    (hf : QBoundedJets r B f) (w : Y) :
    QBoundedJets r (B * ‖w‖) (fun x => f x w) := by
  refine ⟨mul_nonneg hf.nonneg (norm_nonneg w), hf.smooth.clm_apply contDiff_const, ?_⟩
  intro j hj x
  calc
    ‖iteratedFDeriv ℝ j (fun x => f x w) x‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j f x‖ :=
      norm_iteratedFDeriv_clm_apply_const hf.smooth.contDiffAt (by exact_mod_cast hj)
    _ ≤ ‖w‖ * B := mul_le_mul_of_nonneg_left (hf.bound j hj x) (norm_nonneg w)
    _ = B * ‖w‖ := mul_comm _ _

theorem sub {r : ℕ} {B C : ℝ} {f g : X → Y}
    (hf : QBoundedJets r B f) (hg : QBoundedJets r C g) :
    QBoundedJets r (B + C) (fun x => f x - g x) := by
  simpa only [abs_neg, abs_one, one_mul, neg_one_smul, sub_eq_add_neg] using
    hf.add (hg.const_smul (-1))

theorem norm_succ_jet_le_of_directional {n : ℕ} {K : ℝ} {f : X → ℝ}
    (hf : ContDiff ℝ (n + 1) f) (hK : 0 ≤ K) (x : X)
    (h : ∀ w : X, ‖w‖ = 1 → ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y w) x‖ ≤ K) :
    ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ K := by
  have hdf : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [← norm_iteratedFDeriv_fderiv]
  apply ContinuousMultilinearMap.opNorm_le_bound hK
  intro a
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  have heq : iteratedFDeriv ℝ n (fun y => fderiv ℝ f y w) x =
      (ContinuousLinearMap.apply ℝ ℝ w).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fderiv ℝ f) x) := by
    convert! (ContinuousLinearMap.apply ℝ ℝ w).iteratedFDeriv_comp_left hdf.contDiffAt
      (i := n) (by norm_cast) using 1
  have hea := congrArg (fun p => p a) heq
  change iteratedFDeriv ℝ n (fun y => fderiv ℝ f y w) x a =
    iteratedFDeriv ℝ n (fderiv ℝ f) x a w at hea
  rw [← hea]
  exact ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (h w hw) (fun _ => le_rfl)

theorem of_directional {r : ℕ} {K : ℝ} {f : X → ℝ}
    (hK : 0 ≤ K) (hf : ContDiff ℝ (r + 1) f) (h0 : ∀ x, |f x| ≤ K)
    (hD : ∀ w : X, ‖w‖ = 1 → QBoundedJets r K (fun x => fderiv ℝ f x w)) :
    QBoundedJets (r + 1) K f := by
  refine ⟨hK, hf, ?_⟩
  intro j hj x
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h0 x
  | succ j =>
    apply norm_succ_jet_le_of_directional (hf.of_le (by exact_mod_cast hj)) hK x
    intro w hw
    exact (hD w hw).bound j (by omega) x

end QBoundedJets

namespace StepCalculus

local notation "E" => (Fin 3 → ℝ)
variable {r : ℕ} {B C D : ℝ} {f g a : E → ℝ}

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem qPotential_two_step (hf : QPotential 2 B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QPotential 2 (B + 2 * B ^ 2 * ‖v‖ ^ 2) (vectorStep m v f) := by
  have hB : 0 ≤ B := hf.nonneg
  have hgain : 0 ≤ 2 * B ^ 2 * ‖v‖ ^ 2 := by positivity
  refine ⟨by positivity, (vectorStep_regular (hf.boundedDerivs le_rfl) m v).1, ?_⟩
  intro j hj hjr x
  have hjcases : j = 1 ∨ j = 2 := by omega
  rcases hjcases with rfl | rfl
  · simpa only [norm_iteratedFDeriv_one] using
      (norm_fderiv_step_le hf le_rfl m v x).trans (le_add_of_nonneg_right hgain)
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    have h := norm_second_step_le hf le_rfl hm.1 v x hsmall
    have hmB : 2 * m * B ^ 2 * ‖v‖ ^ 2 ≤ 2 * B ^ 2 * ‖v‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hm.2 hgain]
    exact h.trans (add_le_add le_rfl hmB)

private theorem test_memLp (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 1 C g) (m : ℝ) (v x : E) :
    MemLp (fun t : ℝ => g (x + t • v)) 2 (stepLaw m v f x) := by
  let _ := stepLaw_probability hf hr m v x
  exact MemLp.of_bound
    (hg.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable C
    (ae_of_all _ (fun t => hg.abs_le (x + t • v)))

private theorem test_variance_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 1 C g) {m : ℝ} (hm : 0 ≤ m) (v x : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    variance (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) ≤ 2 * C ^ 2 * ‖v‖ ^ 2 := by
  have hgap : 0 < 1 - m * (B * ‖v‖ ^ 2) := by linarith
  have H := spatial_variance_le hf hr hm v x (by linarith) (hg.potential.lipschitzWith le_rfl)
  change variance (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) ≤
    C ^ 2 * ‖v‖ ^ 2 / (1 - m * (B * ‖v‖ ^ 2)) at H
  apply H.trans
  apply (div_le_iff₀ hgap).mpr
  have hnon : 0 ≤ C ^ 2 * ‖v‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hsmall hnon]

theorem abs_test_covariance_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 1 C g) (ha : QBddSmooth 1 D a)
    {m : ℝ} (hm : 0 ≤ m) (v x : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    |covariance (fun t : ℝ => g (x + t • v)) (fun t : ℝ => a (x + t • v))
      (stepLaw m v f x)| ≤ 2 * C * D * ‖v‖ ^ 2 := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  have hC : 0 ≤ C := hg.nonneg
  have hD : 0 ≤ D := ha.nonneg
  by_cases hC0 : C = 0
  · have hg0 : (fun t : ℝ => g (x + t • v)) = 0 := by
      funext t
      exact abs_eq_zero.mp (le_antisymm (by simpa only [hC0] using hg.abs_le (x + t • v)) (abs_nonneg _))
    rw [hg0, covariance_zero_left, abs_zero, hC0]
    simp only [mul_zero, zero_mul, le_refl]
  by_cases hD0 : D = 0
  · have ha0 : (fun t : ℝ => a (x + t • v)) = 0 := by
      funext t
      exact abs_eq_zero.mp (le_antisymm (by simpa only [hD0] using ha.abs_le (x + t • v)) (abs_nonneg _))
    rw [ha0, covariance_zero_right, abs_zero, hD0]
    simp only [mul_zero, zero_mul, le_refl]
  have hCD : 0 < C * D := mul_pos (lt_of_le_of_ne hC (Ne.symm hC0)) (lt_of_le_of_ne hD (Ne.symm hD0))
  have hG := test_memLp hf hr hg m v x
  have hA := test_memLp hf hr ha m v x
  have hplus := variance_nonneg (X := fun t : ℝ => D * g (x + t • v) + C * a (x + t • v)) (μ := μ)
  have hminus := variance_nonneg (X := fun t : ℝ => D * g (x + t • v) - C * a (x + t • v)) (μ := μ)
  rw [variance_fun_add (hG.const_mul D) (hA.const_mul C), variance_const_mul,
    variance_const_mul, covariance_const_mul_left, covariance_const_mul_right] at hplus
  rw [variance_fun_sub (hG.const_mul D) (hA.const_mul C), variance_const_mul,
    variance_const_mul, covariance_const_mul_left, covariance_const_mul_right] at hminus
  have hvg := test_variance_le hf hr hg hm v x hsmall
  have hva := test_variance_le hf hr ha hm v x hsmall
  change variance (fun t : ℝ => g (x + t • v)) μ ≤ _ at hvg
  change variance (fun t : ℝ => a (x + t • v)) μ ≤ _ at hva
  have hweighted : |C * D * covariance (fun t : ℝ => g (x + t • v))
      (fun t : ℝ => a (x + t • v)) μ| ≤ C * D * (2 * C * D * ‖v‖ ^ 2) := by
    apply abs_le.mpr
    constructor <;>
      nlinarith [mul_le_mul_of_nonneg_left hvg (sq_nonneg D),
        mul_le_mul_of_nonneg_left hva (sq_nonneg C)]
  rw [abs_mul, abs_of_pos hCD] at hweighted
  exact (mul_le_mul_iff_right₀ hCD).mp hweighted

def tiltedAverage {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℝ) (v : E) (f : E → ℝ) (g : E → F) (x : E) : F :=
  ∫ t : ℝ, g (x + t • v) ∂stepLaw m v f x

section Banach

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {g : E → F}

theorem norm_tiltedAverage_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {C : ℝ} (hg : ∀ y, ‖g y‖ ≤ C) (m : ℝ) (v x : E) :
    ‖tiltedAverage m v f g x‖ ≤ C := by
  let _ := stepLaw_probability hf hr m v x
  simpa only [tiltedAverage, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := stepLaw m v f x) (ae_of_all _ (fun t => hg (x + t • v))))

theorem tiltedAverage_c1 (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBoundedJets 1 C g) (m : ℝ) (v : E) :
    ContDiff ℝ 1 (tiltedAverage m v f g) ∧ ∀ x,
      HasFDerivAt (tiltedAverage m v f g)
        (∫ t : ℝ, fderiv ℝ g (x + t • v) + m •
          (fderiv ℝ f (x + t • v) - fderiv ℝ (vectorStep m v f) x).smulRight
            (g (x + t • v)) ∂stepLaw m v f x) x := by
  let T := vectorStep m v f
  let L : E × ℝ →L[ℝ] E := vectorTranslation v
  let H : E × ℝ → ℝ := fun z => f (L z) - T z.1
  let W : E × ℝ → ℝ := fun z => Real.exp (m * H z)
  let U : E × ℝ → E →L[ℝ] F := fun z => fderiv ℝ g (L z) + m •
    (fderiv ℝ f (L z) - fderiv ℝ T z.1).smulRight (g (L z))
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hb := hf.boundedDerivs hr
  have hT : BoundedDerivs T := vectorStep_regular hb m v
  have hH : BoundedDerivs H := by
    simpa only [H, sub_eq_add_neg, neg_one_mul, ContinuousLinearMap.coe_fst'] using
      (hb.compCLM L).add ((hT.compCLM (ContinuousLinearMap.fst ℝ E ℝ)).const_mul (-1))
  have hW : Continuous W := Real.continuous_exp.comp (continuous_const.mul hH.1.continuous)
  have hWE : HasExpGrowth W := (hH.exp_growths m).1
  have hgc : Continuous (fun z : E × ℝ => g (L z)) := hg.smooth.continuous.comp L.continuous
  have hgdc : Continuous (fun z : E × ℝ => fderiv ℝ g (L z)) :=
    (hg.smooth.continuous_fderiv (by norm_num)).comp L.continuous
  have hfc : Continuous (fun z : E × ℝ => fderiv ℝ f (L z) - fderiv ℝ T z.1) :=
    ((hb.1.continuous_fderiv (by norm_num)).comp L.continuous).sub
      ((hT.1.continuous_fderiv (by norm_num)).comp continuous_fst)
  have hUc : Continuous U := hgdc.add
    ((((ContinuousLinearMap.smulRightL ℝ E F).continuous.comp hfc).clm_apply hgc).const_smul m)
  have hUbound (z : E × ℝ) : ‖U z‖ ≤ C + |m| * (2 * B * C) := by
    have hdf : ‖fderiv ℝ f (L z) - fderiv ℝ T z.1‖ ≤ 2 * B := by
      exact (norm_sub_le _ _).trans (by
        linarith [hf.fderiv_le (by omega) (L z), norm_fderiv_step_le hf hr m v z.1])
    calc
      ‖U z‖ ≤ ‖fderiv ℝ g (L z)‖ +
          ‖m • (fderiv ℝ f (L z) - fderiv ℝ T z.1).smulRight (g (L z))‖ := norm_add_le _ _
      _ ≤ C + |m| * (2 * B * C) := by
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
        exact add_le_add (hg.derivativeJets.norm_le (L z))
          (mul_le_mul_of_nonneg_left
            (mul_le_mul hdf (hg.norm_le (L z)) (norm_nonneg _) (by positivity)) (abs_nonneg m))
  have hUE : HasExpGrowth U := HasExpGrowth.of_bounded (by positivity) hUbound
  have hGE : HasExpGrowth (fun z : E × ℝ => g (L z)) :=
    HasExpGrowth.of_bounded hC (fun z => hg.norm_le (L z))
  have hdg : Differentiable ℝ g := hg.smooth.differentiable (by norm_num)
  have hdf : Differentiable ℝ f := hb.1.differentiable (by norm_num)
  have hdT : Differentiable ℝ T := hT.1.differentiable (by norm_num)
  have hdiff (x : E) (t : ℝ) :
      HasFDerivAt (fun y => W (y,t) • g (L (y,t))) (W (x,t) • U (x,t)) x := by
    have hline : HasFDerivAt (fun y : E => y + t • v) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).add_const (t • v)
    have hfx : HasFDerivAt (fun y : E => f (y + t • v)) (fderiv ℝ f (x + t • v)) x := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        (hdf (x + t • v)).hasFDerivAt.comp x hline
    have hgx : HasFDerivAt (fun y : E => g (y + t • v)) (fderiv ℝ g (x + t • v)) x := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        (hdg (x + t • v)).hasFDerivAt.comp x hline
    convert! (((hfx.sub (hdT x).hasFDerivAt).const_mul m).exp).smul hgx using 1
    ext w
    simp only [U, W, H, L, vectorTranslation, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    module
  let J : E → F := fun x => ∫ t : ℝ, W (x,t) • g (L (x,t)) ∂gaussianReal 0 1
  let A : E → E →L[ℝ] F := fun x => ∫ t : ℝ, U (x,t) ∂stepLaw m v f x
  have hJ (x : E) : HasFDerivAt J (A x) x := by
    have hd := hasFDerivAt_gaussian_integral (fun z : E × ℝ => W z • g (L z))
      (fun z => W z • U z) (hW.smul hgc) (hW.smul hUc) (hWE.smul hGE) (hWE.smul hUE) hdiff x
    convert hd using 1
    exact gaussianStepLaw_integral (hb.compCLM L) m x (fun t => U (x,t))
  have heq : tiltedAverage m v f g = J := by
    funext x
    exact gaussianStepLaw_integral (hb.compCLM L) m x (fun t => g (x + t • v))
  have hAc : Continuous A := gaussianAverage_continuous (hb.compCLM L) m hUc (by positivity) hUbound
  rw [heq]
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨A, hAc, hJ⟩, ?_⟩
  intro x
  exact hJ x

theorem tiltedAverage_apply {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a : E → G →L[ℝ] F} (hf : QPotential r B f) (hr : 2 ≤ r)
    {s : ℕ} (ha : QBoundedJets s C a) (m : ℝ) (v x : E) (w : G) :
    tiltedAverage m v f a x w = tiltedAverage m v f (fun y => a y w) x := by
  let _ := stepLaw_probability hf hr m v x
  have hi : Integrable (fun t : ℝ => a (x + t • v)) (stepLaw m v f x) :=
    Integrable.of_bound
      (ha.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable C
      (ae_of_all _ (fun t => ha.norm_le (x + t • v)))
  exact ContinuousLinearMap.integral_apply hi w

theorem integrable_tilted_shift (hf : QPotential r B f) (hr : 2 ≤ r)
    {s : ℕ} (hg : QBoundedJets s C g) (m : ℝ) (v x : E) :
    Integrable (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) := by
  let _ := stepLaw_probability hf hr m v x
  exact Integrable.of_bound
    (hg.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable C
    (ae_of_all _ (fun t => hg.norm_le (x + t • v)))

end Banach

theorem fderiv_step_eq_tiltedAverage (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) (v : E) :
    fderiv ℝ (vectorStep m v f) = tiltedAverage m v f (fderiv ℝ f) := by
  funext x
  ext w
  rw [fderiv_step_apply hf hr, tiltedAverage_apply hf hr (hf.of_le hr).derivativeJets]
  rfl

theorem fderiv_tiltedAverage_apply (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 1 C g) (m : ℝ) (v x w : E) :
    fderiv ℝ (tiltedAverage m v f g) x w =
      noiseMean m v f x (fun t => fderiv ℝ g (x + t • v) w) + m *
        covariance (fun t : ℝ => g (x + t • v))
          (fun t : ℝ => fderiv ℝ f (x + t • v) w) (stepLaw m v f x) := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  let T := vectorStep m v f
  let K : ℝ → E →L[ℝ] ℝ := fun t => fderiv ℝ g (x + t • v) + m •
    (fderiv ℝ f (x + t • v) - fderiv ℝ T x).smulRight (g (x + t • v))
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hgc : Continuous (fun t : ℝ => g (x + t • v)) :=
    hg.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hdgc : Continuous (fun t : ℝ => fderiv ℝ g (x + t • v)) :=
    (hg.smooth.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hdfc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • v)) :=
    ((hf.boundedDerivs hr).1.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hKc : Continuous K := hdgc.add
    ((((ContinuousLinearMap.smulRightL ℝ E ℝ).continuous.comp
      (hdfc.sub continuous_const)).clm_apply hgc).const_smul m)
  have hKb (t : ℝ) : ‖K t‖ ≤ C + |m| * (2 * B * C) := by
    have hdf : ‖fderiv ℝ f (x + t • v) - fderiv ℝ T x‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by
        linarith [hf.fderiv_le (by omega) (x + t • v), norm_fderiv_step_le hf hr m v x])
    calc
      ‖K t‖ ≤ ‖fderiv ℝ g (x + t • v)‖ +
          ‖m • (fderiv ℝ f (x + t • v) - fderiv ℝ T x).smulRight (g (x + t • v))‖ := norm_add_le _ _
      _ ≤ C + |m| * (2 * B * C) := by
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
        exact add_le_add (hg.potential.fderiv_le le_rfl _)
          (mul_le_mul_of_nonneg_left
            (mul_le_mul hdf (hg.abs_le _) (abs_nonneg _) (by positivity)) (abs_nonneg m))
  have hiK : Integrable K μ := Integrable.of_bound hKc.aestronglyMeasurable _ (ae_of_all _ hKb)
  have hG := test_memLp hf hr hg m v x
  have ha : QBddSmooth 1 (B * ‖w‖) (fun y => fderiv ℝ f y w) := (hf.of_le hr).directional w
  have hA := test_memLp hf hr ha m v x
  have hiD : Integrable (fun t : ℝ => fderiv ℝ g (x + t • v) w) μ :=
    Integrable.of_bound (hdgc.clm_apply continuous_const).aestronglyMeasurable (C * ‖w‖)
      (ae_of_all _ (fun t => hg.potential.directional_le le_rfl (x + t • v) w))
  have hiP : Integrable (fun t : ℝ => g (x + t • v) * fderiv ℝ f (x + t • v) w) μ :=
    hG.integrable_mul hA
  have hiQ := (hG.integrable (by norm_num)).mul_const (fderiv ℝ T x w)
  rw [((tiltedAverage_c1 hf hr (qBoundedJets_iff_qBddSmooth.mpr hg) m v).2 x).fderiv]
  change (∫ t : ℝ, K t ∂μ) w = _
  rw [ContinuousLinearMap.integral_apply hiK]
  calc
    (∫ t : ℝ, K t w ∂μ) = ∫ t : ℝ, fderiv ℝ g (x + t • v) w + m *
        (g (x + t • v) * fderiv ℝ f (x + t • v) w -
          g (x + t • v) * fderiv ℝ T x w) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        dsimp only [K]
        simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
        ring)
    _ = noiseMean m v f x (fun t => fderiv ℝ g (x + t • v) w) + m *
        covariance (fun t : ℝ => g (x + t • v))
          (fun t : ℝ => fderiv ℝ f (x + t • v) w) μ := by
      rw [integral_add (f := fun t : ℝ => fderiv ℝ g (x + t • v) w)
        (g := fun t : ℝ => m * (g (x + t • v) * fderiv ℝ f (x + t • v) w -
          g (x + t • v) * fderiv ℝ T x w)) hiD ((hiP.sub hiQ).const_mul m), integral_const_mul,
        integral_sub (f := fun t : ℝ => g (x + t • v) * fderiv ℝ f (x + t • v) w)
          (g := fun t : ℝ => g (x + t • v) * fderiv ℝ T x w) hiP hiQ, integral_mul_const, covariance_eq_sub hG hA,
        fderiv_step_apply hf hr]
      rfl

theorem qbddSmooth_one_tiltedAverage (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 1 C g) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBddSmooth 1 (C + 2 * B * C * ‖v‖ ^ 2) (tiltedAverage m v f g) := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hgain : 0 ≤ 2 * B * C * ‖v‖ ^ 2 := by positivity
  refine ⟨by positivity, (tiltedAverage_c1 hf hr (qBoundedJets_iff_qBddSmooth.mpr hg) m v).1, ?_⟩
  intro j hj x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [norm_iteratedFDeriv_zero]
    exact (norm_tiltedAverage_le hf hr (fun y => hg.abs_le y) m v x).trans (le_add_of_nonneg_right hgain)
  · rw [norm_iteratedFDeriv_one]
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro w hw
    have ha : QBddSmooth 1 B (fun y => fderiv ℝ f y w) := by
      simpa only [hw, mul_one] using (hf.of_le hr).directional w
    have hcov := abs_test_covariance_le hf hr hg ha hm.1 v x hsmall
    have hbase := abs_noiseMean_le hf hr m v x (fun t => hg.potential.directional_le le_rfl (x + t • v) w)
    rw [hw, mul_one] at hbase
    rw [Real.norm_eq_abs, fderiv_tiltedAverage_apply hf hr hg]
    calc
      _ ≤ |noiseMean m v f x (fun t => fderiv ℝ g (x + t • v) w)| +
          |m * covariance (fun t : ℝ => g (x + t • v))
            (fun t : ℝ => fderiv ℝ f (x + t • v) w) (stepLaw m v f x)| := abs_add_le _ _
      _ ≤ C + m * (2 * C * B * ‖v‖ ^ 2) := by
        rw [abs_mul, abs_of_nonneg hm.1]
        exact add_le_add hbase (mul_le_mul_of_nonneg_left hcov hm.1)
      _ ≤ C + 2 * B * C * ‖v‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hm.2 hgain]

section HigherSmoothness

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {g : E → F}

theorem fderiv_tiltedAverage (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBoundedJets 1 C g) (m : ℝ) (v : E) :
    fderiv ℝ (tiltedAverage m v f g) = fun x =>
      tiltedAverage m v f (fderiv ℝ g) x + m •
        (tiltedAverage m v f (fun y => (fderiv ℝ f y).smulRight (g y)) x -
          (tiltedAverage m v f (fderiv ℝ f) x).smulRight (tiltedAverage m v f g x)) := by
  funext x
  let μ := stepLaw m v f x
  let R : F →L[ℝ] E →L[ℝ] F :=
    ContinuousLinearMap.smulRightL ℝ E F (fderiv ℝ (vectorStep m v f) x)
  have ha : QBoundedJets 1 B (fderiv ℝ f) := (hf.of_le hr).derivativeJets
  have hiG := integrable_tilted_shift hf hr hg m v x
  have hiD := integrable_tilted_shift hf hr hg.derivativeJets m v x
  have hiP := integrable_tilted_shift hf hr (ha.smulRight hg) m v x
  have hiQ : Integrable (fun t : ℝ => R (g (x + t • v))) μ := R.integrable_comp hiG
  rw [((tiltedAverage_c1 hf hr hg m v).2 x).fderiv]
  calc
    (∫ t : ℝ, fderiv ℝ g (x + t • v) + m •
        (fderiv ℝ f (x + t • v) - fderiv ℝ (vectorStep m v f) x).smulRight
          (g (x + t • v)) ∂μ) =
      ∫ t : ℝ, fderiv ℝ g (x + t • v) + m •
        ((fderiv ℝ f (x + t • v)).smulRight (g (x + t • v)) - R (g (x + t • v))) ∂μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      ext w
      change fderiv ℝ g (x + t • v) w +
          m • ((fderiv ℝ f (x + t • v) w - fderiv ℝ (vectorStep m v f) x w) • g (x + t • v)) =
        fderiv ℝ g (x + t • v) w + m •
          (fderiv ℝ f (x + t • v) w • g (x + t • v) -
            fderiv ℝ (vectorStep m v f) x w • g (x + t • v))
      module
    _ = tiltedAverage m v f (fderiv ℝ g) x + m •
        (tiltedAverage m v f (fun y => (fderiv ℝ f y).smulRight (g y)) x -
          (tiltedAverage m v f (fderiv ℝ f) x).smulRight (tiltedAverage m v f g x)) := by
      rw [integral_add (f := fun t : ℝ => fderiv ℝ g (x + t • v))
        (g := fun t : ℝ => m • ((fderiv ℝ f (x + t • v)).smulRight (g (x + t • v)) -
          R (g (x + t • v)))) hiD ((hiP.sub hiQ).smul m), integral_smul,
        integral_sub (f := fun t : ℝ => (fderiv ℝ f (x + t • v)).smulRight (g (x + t • v)))
          (g := fun t : ℝ => R (g (x + t • v))) hiP hiQ, R.integral_comp_comm hiG]
      change tiltedAverage m v f (fderiv ℝ g) x + m •
        (tiltedAverage m v f (fun y => (fderiv ℝ f y).smulRight (g y)) x -
          (fderiv ℝ (vectorStep m v f) x).smulRight (tiltedAverage m v f g x)) = _
      rw [fderiv_step_eq_tiltedAverage hf hr]

theorem tiltedAverage_smooth (n : ℕ) (hf : QPotential r B f) (hr : 2 ≤ r)
    (hn : n ≤ r) (hg : QBoundedJets n C g) (m : ℝ) (v : E) :
    ContDiff ℝ n (tiltedAverage m v f g) := by
  induction n generalizing F C with
  | zero =>
    apply contDiff_zero.mpr
    exact gaussianAverage_continuous ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) m
      (hg.smooth.continuous.comp (vectorTranslation v).continuous) hg.nonneg
      (fun z => hg.norm_le ((vectorTranslation v) z))
  | succ n ih =>
    have hfg : QBoundedJets n B (fderiv ℝ f) := (hf.of_le hn).derivativeJets
    have hgl : QBoundedJets n C g := hg.of_le (by omega)
    have hD : ContDiff ℝ n (tiltedAverage m v f (fderiv ℝ g)) := ih (by omega) hg.derivativeJets
    have hG : ContDiff ℝ n (tiltedAverage m v f g) := ih (by omega) hgl
    have hA : ContDiff ℝ n (tiltedAverage m v f (fderiv ℝ f)) := ih (by omega) hfg
    have hP : ContDiff ℝ n
        (tiltedAverage m v f (fun y => (fderiv ℝ f y).smulRight (g y))) :=
      ih (by omega) (hfg.smulRight hgl)
    have hder : ContDiff ℝ n (fderiv ℝ (tiltedAverage m v f g)) := by
      rw [fderiv_tiltedAverage hf hr (hg.of_le (by omega)) m v]
      have hTensor : ContDiff ℝ n (fun x =>
          (tiltedAverage m v f (fderiv ℝ f) x).smulRight (tiltedAverage m v f g x)) := by
        convert! (((ContinuousLinearMap.smulRightL ℝ E F).contDiff.comp hA).clm_apply hG) using 1
      exact hD.add ((hP.sub hTensor).const_smul m)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fderiv ℝ (tiltedAverage m v f g), hder,
      fun x => ((tiltedAverage_c1 hf hr (hg.of_le (by omega)) m v).2 x).differentiableAt.hasFDerivAt⟩

end HigherSmoothness

theorem contDiff_step (hf : QPotential (r + 2) B f) (m : ℝ) (v : E) :
    ContDiff ℝ (r + 2) (vectorStep m v f) := by
  have hd : ContDiff ℝ (r + 1) (tiltedAverage m v f (fderiv ℝ f)) :=
    tiltedAverage_smooth (r + 1) hf (by omega) (by omega) hf.derivativeJets m v
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨tiltedAverage m v f (fderiv ℝ f), hd, ?_⟩
  intro x
  rw [← fderiv_step_eq_tiltedAverage hf (by omega) m v]
  exact ((vectorStep_regular (hf.boundedDerivs (by omega)) m v).1.differentiable (by norm_num) x).hasFDerivAt

private theorem sub_const_one {g : E → ℝ} (hg : QBddSmooth 1 C g) {c : ℝ} (hc : |c| ≤ C) :
    QBddSmooth 1 (2 * C) (fun y => g y - c) := by
  have hC : 0 ≤ C := hg.nonneg
  refine ⟨by positivity, hg.smooth.sub contDiff_const, ?_⟩
  intro j hj y
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [norm_iteratedFDeriv_zero]
    exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs] using
      (add_le_add (hg.abs_le y) hc).trans_eq (by ring))
  · rw [norm_iteratedFDeriv_one,
      ((hg.smooth.differentiable (by norm_num) y).hasFDerivAt.sub_const c).fderiv]
    exact (hg.potential.fderiv_le le_rfl y).trans (by linarith)

private theorem covariance_product_centered {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {G H A : ℝ → ℝ} (hG : MemLp G 2 μ) (hH : MemLp H 2 μ) (hA : MemLp A 2 μ)
    (hGH : MemLp (G * H) 2 μ) (c d : ℝ) :
    covariance (fun t => (G t - c) * (H t - d)) A μ =
      covariance (G * H) A μ - c * covariance H A μ - d * covariance G A μ := by
  let L := G * H - c • H - d • G
  have hL : MemLp L 2 μ := (hGH.sub (hH.const_mul c)).sub (hG.const_mul d)
  have heq : (fun t => (G t - c) * (H t - d)) = fun t => L t + c * d := by
    funext t
    simp only [L, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, covariance_add_const_left (hL.integrable (by norm_num)) (c * d)]
  change covariance (G * H - c • H - d • G) A μ = _
  rw [covariance_sub_left (X := G * H - c • H) (Y := d • G)
      (hGH.sub (hH.const_mul c)) (hG.const_mul d) hA,
    covariance_sub_left (X := G * H) (Y := c • H) hGH (hH.const_mul c) hA, covariance_smul_left, covariance_smul_left]

def spatialCovariance (m : ℝ) (v : E) (f g a : E → ℝ) (x : E) : ℝ :=
  tiltedAverage m v f (fun y => g y * a y) x -
    tiltedAverage m v f g x * tiltedAverage m v f a x

theorem spatialCovariance_eq (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 1 C g) (ha : QBddSmooth 1 D a) (m : ℝ) (v x : E) :
    spatialCovariance m v f g a x =
      covariance (fun t : ℝ => g (x + t • v)) (fun t : ℝ => a (x + t • v)) (stepLaw m v f x) := by
  let _ := stepLaw_probability hf hr m v x
  rw [covariance_eq_sub (test_memLp hf hr hg m v x) (test_memLp hf hr ha m v x)]
  rfl

theorem fderiv_spatialCovariance_apply (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 2 C g) (ha : QBddSmooth 2 D a) (m : ℝ) (v x w : E) :
    fderiv ℝ (spatialCovariance m v f g a) x w =
      covariance (fun t : ℝ => fderiv ℝ g (x + t • v) w)
        (fun t : ℝ => a (x + t • v)) (stepLaw m v f x) +
      covariance (fun t : ℝ => g (x + t • v))
        (fun t : ℝ => fderiv ℝ a (x + t • v) w) (stepLaw m v f x) + m *
      covariance (fun t : ℝ =>
        (g (x + t • v) - tiltedAverage m v f g x) *
          (a (x + t • v) - tiltedAverage m v f a x))
        (fun t : ℝ => fderiv ℝ f (x + t • v) w) (stepLaw m v f x) := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  have hg1 := hg.of_le (by omega : 1 ≤ 2)
  have ha1 := ha.of_le (by omega : 1 ≤ 2)
  have hpg : QBddSmooth 1 ((2 : ℝ) * C * D) (fun y => g y * a y) := by
    simpa only [pow_one] using qBoundedJets_iff_qBddSmooth.mp
      ((qBoundedJets_iff_qBddSmooth.mpr hg1).mul (qBoundedJets_iff_qBddSmooth.mpr ha1))
  have hG := test_memLp hf hr hg1 m v x
  have hA := test_memLp hf hr ha1 m v x
  have hS := test_memLp hf hr ((hf.of_le hr).directional w) m v x
  have hP := test_memLp hf hr hpg m v x
  have hdg : QBddSmooth 1 (C * ‖w‖) (fun y => fderiv ℝ g y w) := hg.potential.directional w
  have hda : QBddSmooth 1 (D * ‖w‖) (fun y => fderiv ℝ a y w) := ha.potential.directional w
  have hDG := test_memLp hf hr hdg m v x
  have hDA := test_memLp hf hr hda m v x
  have hpD : Integrable (fun t : ℝ => fderiv ℝ g (x + t • v) w * a (x + t • v)) μ := hDG.integrable_mul hA
  have hqD : Integrable (fun t : ℝ => g (x + t • v) * fderiv ℝ a (x + t • v) w) μ := hG.integrable_mul hDA
  have hDiffG := ((tiltedAverage_c1 hf hr (qBoundedJets_iff_qBddSmooth.mpr hg1) m v).2 x).differentiableAt
  have hDiffA := ((tiltedAverage_c1 hf hr (qBoundedJets_iff_qBddSmooth.mpr ha1) m v).2 x).differentiableAt
  have hDiffP := ((tiltedAverage_c1 hf hr (qBoundedJets_iff_qBddSmooth.mpr hpg) m v).2 x).differentiableAt
  have hd := hDiffP.hasFDerivAt.sub (hDiffG.hasFDerivAt.mul hDiffA.hasFDerivAt)
  have hprod (y : E) : fderiv ℝ (fun y => g y * a y) y w =
      fderiv ℝ g y w * a y + g y * fderiv ℝ a y w := by
    change fderiv ℝ (g * a) y w = _
    rw [((hg.smooth.differentiable (by norm_num) y).hasFDerivAt.mul
      (ha.smooth.differentiable (by norm_num) y).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  change fderiv ℝ (tiltedAverage m v f (fun z => g z * a z) -
    tiltedAverage m v f g * tiltedAverage m v f a) x w = _
  rw [hd.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_tiltedAverage_apply hf hr hpg, fderiv_tiltedAverage_apply hf hr hg1,
    fderiv_tiltedAverage_apply hf hr ha1]
  simp_rw [noiseMean, hprod]
  rw [integral_add hpD hqD,
    covariance_product_centered hG hA hS hP,
    covariance_eq_sub hDG hA, covariance_eq_sub hG hDA]
  simp only [tiltedAverage, Pi.mul_def, μ]
  ring

theorem abs_fderiv_spatialCovariance_apply_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 2 C g) (ha : QBddSmooth 2 D a)
    {m : ℝ} (hm : 0 ≤ m) (v x w : E) (hw : ‖w‖ = 1)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    |fderiv ℝ (spatialCovariance m v f g a) x w| ≤
      (4 * C * D + 16 * m * B * C * D) * ‖v‖ ^ 2 := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hD : 0 ≤ D := ha.nonneg
  have hg1 := hg.of_le (by omega : 1 ≤ 2)
  have ha1 := ha.of_le (by omega : 1 ≤ 2)
  have hdg : QBddSmooth 1 C (fun y => fderiv ℝ g y w) := by
    simpa only [hw, mul_one] using hg.potential.directional w
  have hda : QBddSmooth 1 D (fun y => fderiv ℝ a y w) := by
    simpa only [hw, mul_one] using ha.potential.directional w
  have hs : QBddSmooth 1 B (fun y => fderiv ℝ f y w) := by
    simpa only [hw, mul_one] using (hf.of_le hr).directional w
  have hmg : |tiltedAverage m v f g x| ≤ C := by
    simpa only [Real.norm_eq_abs] using norm_tiltedAverage_le (g := g) hf hr (fun y => hg.abs_le y) m v x
  have hma : |tiltedAverage m v f a x| ≤ D := by
    simpa only [Real.norm_eq_abs] using norm_tiltedAverage_le (g := a) hf hr (fun y => ha.abs_le y) m v x
  have hcent : QBddSmooth 1 (8 * C * D) (fun y =>
      (g y - tiltedAverage m v f g x) * (a y - tiltedAverage m v f a x)) := by
    have h := (qBoundedJets_iff_qBddSmooth.mpr (sub_const_one hg1 hmg)).mul
      (qBoundedJets_iff_qBddSmooth.mpr (sub_const_one ha1 hma))
    convert qBoundedJets_iff_qBddSmooth.mp h using 1
    ring
  have h₁ := abs_test_covariance_le hf hr hdg ha1 hm v x hsmall
  have h₂ := abs_test_covariance_le hf hr hg1 hda hm v x hsmall
  have h₃ := abs_test_covariance_le hf hr hcent hs hm v x hsmall
  rw [fderiv_spatialCovariance_apply hf hr hg ha]
  calc
    _ ≤ |covariance (fun t : ℝ => fderiv ℝ g (x + t • v) w)
          (fun t : ℝ => a (x + t • v)) (stepLaw m v f x)| +
        |covariance (fun t : ℝ => g (x + t • v))
          (fun t : ℝ => fderiv ℝ a (x + t • v) w) (stepLaw m v f x)| +
        |m * covariance (fun t : ℝ =>
          (g (x + t • v) - tiltedAverage m v f g x) *
            (a (x + t • v) - tiltedAverage m v f a x))
          (fun t : ℝ => fderiv ℝ f (x + t • v) w) (stepLaw m v f x)| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ 2 * C * D * ‖v‖ ^ 2 + 2 * C * D * ‖v‖ ^ 2 +
        m * (2 * (8 * C * D) * B * ‖v‖ ^ 2) := by
      rw [abs_mul, abs_of_nonneg hm]
      exact add_le_add (add_le_add h₁ h₂) (mul_le_mul_of_nonneg_left h₃ hm)
    _ = _ := by ring

private theorem fderiv_apply_const {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {a : E → F →L[ℝ] G}
    (ha : Differentiable ℝ a) (x : E) (w : F) (u : E) :
    fderiv ℝ (fun y => a y w) x u = fderiv ℝ a x u w := by
  have hd := ((ContinuousLinearMap.apply ℝ G w).hasFDerivAt.comp x (ha x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => a y w) x = _ at hd
  rw [hd]
  rfl

private theorem fderiv_apply₂_const {F G H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a : E → F →L[ℝ] G →L[ℝ] H} (ha : Differentiable ℝ a) (x : E) (w : F) (u : G) (z : E) :
    fderiv ℝ (fun y => a y w u) x z = fderiv ℝ a x z w u := by
  rw [fderiv_apply_const (ha.clm_apply (differentiable_const w)) x u z,
    fderiv_apply_const ha x w z]

theorem spatialCovariance_contDiff_one (hf : QPotential r B f) (hr : 2 ≤ r)
    (hg : QBddSmooth 1 C g) (ha : QBddSmooth 1 D a) (m : ℝ) (v : E) :
    ContDiff ℝ 1 (spatialCovariance m v f g a) := by
  have hG := qBoundedJets_iff_qBddSmooth.mpr hg
  have hA := qBoundedJets_iff_qBddSmooth.mpr ha
  exact (tiltedAverage_c1 hf hr (hG.mul hA) m v).1.sub
    ((tiltedAverage_c1 hf hr hG m v).1.mul (tiltedAverage_c1 hf hr hA m v).1)

theorem norm_second_tiltedAverage_le (hf : QPotential 3 B f) (hg : QBddSmooth 2 C g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    ‖fderiv ℝ (fderiv ℝ (tiltedAverage m v f g)) x‖ ≤
      C + (6 * B + 16 * B ^ 2) * C * ‖v‖ ^ 2 := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hs : ContDiff ℝ 2 (tiltedAverage m v f g) :=
    tiltedAverage_smooth 2 hf (by omega) (by omega) (qBoundedJets_iff_qBddSmooth.mpr hg) m v
  have hd : Differentiable ℝ (fderiv ℝ (tiltedAverage m v f g)) :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hK : 0 ≤ C + (6 * B + 16 * B ^ 2) * C * ‖v‖ ^ 2 := by positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hK
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hK
  intro w hw
  have hg1 := hg.of_le (by omega : 1 ≤ 2)
  have hdg : QBddSmooth 1 C (fun y => fderiv ℝ g y w) := by
    simpa only [hw, mul_one] using hg.potential.directional w
  have ha : QBddSmooth 2 B (fun y => fderiv ℝ f y w) := by
    simpa only [hw, mul_one] using hf.directional w
  have ha1 := ha.of_le (by omega : 1 ≤ 2)
  have hscore : QBddSmooth 1 B (fun y => fderiv ℝ f y u) := by
    simpa only [hu, mul_one] using (hf.of_le (by omega : 2 ≤ 3)).directional u
  have heq : (fun y => fderiv ℝ (tiltedAverage m v f g) y w) = fun y =>
      tiltedAverage m v f (fun z => fderiv ℝ g z w) y +
        m * spatialCovariance m v f g (fun z => fderiv ℝ f z w) y := by
    funext y
    rw [fderiv_tiltedAverage_apply hf (by omega) hg1,
      spatialCovariance_eq hf (by omega) hg1 ha1]
    rfl
  have hD := ((tiltedAverage_c1 hf (by omega) (qBoundedJets_iff_qBddSmooth.mpr hdg) m v).2 x).differentiableAt
  have hCov := (spatialCovariance_contDiff_one hf (by omega) hg1 ha1 m v).differentiable (by norm_num) x
  have hDer := hD.hasFDerivAt.add (hCov.hasFDerivAt.const_mul m)
  have hbase := abs_noiseMean_le hf (by omega) m v x
    (fun t => hdg.potential.directional_le le_rfl (x + t • v) u)
  rw [hu, mul_one] at hbase
  have hcov := abs_test_covariance_le hf (by omega) hdg hscore hm.1 v x hsmall
  have hdcov := abs_fderiv_spatialCovariance_apply_le hf (by omega) hg ha hm.1 v x u hu hsmall
  rw [Real.norm_eq_abs, ← fderiv_apply_const hd x w u, heq]
  change |fderiv ℝ (tiltedAverage m v f (fun z => fderiv ℝ g z w) +
    (fun y => m * spatialCovariance m v f g (fun z => fderiv ℝ f z w) y)) x u| ≤ _
  rw [hDer.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_tiltedAverage_apply hf (by omega) hdg]
  calc
    _ ≤ |noiseMean m v f x (fun t => fderiv ℝ (fun z => fderiv ℝ g z w) (x + t • v) u)| +
        |m * covariance (fun t : ℝ => fderiv ℝ g (x + t • v) w)
          (fun t : ℝ => fderiv ℝ f (x + t • v) u) (stepLaw m v f x)| +
        |m * fderiv ℝ (spatialCovariance m v f g (fun z => fderiv ℝ f z w)) x u| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ C + m * (2 * C * B * ‖v‖ ^ 2) +
        m * ((4 * C * B + 16 * m * B * C * B) * ‖v‖ ^ 2) := by
      rw [abs_mul, abs_of_nonneg hm.1, abs_mul, abs_of_nonneg hm.1]
      exact add_le_add (add_le_add hbase (mul_le_mul_of_nonneg_left hcov hm.1))
        (mul_le_mul_of_nonneg_left hdcov hm.1)
    _ ≤ C + (6 * B + 16 * B ^ 2) * C * ‖v‖ ^ 2 := by
      have hm2 : m ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
      nlinarith [mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 6 * B * C * ‖v‖ ^ 2),
        mul_le_mul_of_nonneg_right hm2 (by positivity : 0 ≤ 16 * B ^ 2 * C * ‖v‖ ^ 2)]

theorem qbddSmooth_two_tiltedAverage (hf : QPotential 3 B f) (hg : QBddSmooth 2 C g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBddSmooth 2 (C + (6 * B + 16 * B ^ 2) * C * ‖v‖ ^ 2) (tiltedAverage m v f g) := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hgain : 0 ≤ (6 * B + 16 * B ^ 2) * C * ‖v‖ ^ 2 := by positivity
  refine ⟨by positivity,
    tiltedAverage_smooth 2 hf (by omega) (by omega) (qBoundedJets_iff_qBddSmooth.mpr hg) m v, ?_⟩
  intro j hj x
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    exact (norm_tiltedAverage_le hf (by omega) (fun y => hg.abs_le y) m v x).trans
      (le_add_of_nonneg_right hgain)
  · have h := (qbddSmooth_one_tiltedAverage hf (by omega) (hg.of_le (by omega)) hm v hsmall).bound 1 le_rfl x
    exact h.trans (by nlinarith [mul_nonneg (sq_nonneg B) (mul_nonneg hC (sq_nonneg ‖v‖))])
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    exact norm_second_tiltedAverage_le hf hg hm v x hsmall

def stepStabilityThreeCoefficient (B : ℝ) : ℝ := 6 * B ^ 2 + 16 * B ^ 3

theorem norm_third_step_le (hf : QPotential 3 B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (vectorStep m v f))) x‖ ≤
      B + stepStabilityThreeCoefficient B * ‖v‖ ^ 2 := by
  let T := vectorStep m v f
  have hB : 0 ≤ B := hf.nonneg
  have hs : ContDiff ℝ 3 T := contDiff_step (r := 1) hf m v
  have hD : Differentiable ℝ (fderiv ℝ T) :=
    (hs.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have hDD : Differentiable ℝ (fderiv ℝ (fderiv ℝ T)) :=
    ((hs.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hK : 0 ≤ B + stepStabilityThreeCoefficient B * ‖v‖ ^ 2 := by
    dsimp only [stepStabilityThreeCoefficient]
    positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hK
  intro z hz
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hK
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hK
  intro w hw
  have hgw : QBddSmooth 2 B (fun y => fderiv ℝ f y w) := by
    simpa only [hw, mul_one] using hf.directional w
  let G := tiltedAverage m v f (fun y => fderiv ℝ f y w)
  have hGs : ContDiff ℝ 2 G := tiltedAverage_smooth 2 hf (by omega) (by omega)
    (qBoundedJets_iff_qBddSmooth.mpr hgw) m v
  have hGD : Differentiable ℝ (fderiv ℝ G) :=
    (hGs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hF : (fun y => fderiv ℝ T y w) = G := by
    funext y
    rw [fderiv_step_eq_tiltedAverage hf (by omega) m v,
      tiltedAverage_apply hf (by omega) hf.derivativeJets]
  have hH : (fun y => fderiv ℝ (fderiv ℝ T) y u w) = fun y => fderiv ℝ G y u := by
    funext y
    rw [← fderiv_apply_const hD y w u, hF]
  have heq : fderiv ℝ (fderiv ℝ (fderiv ℝ T)) x z u w =
      fderiv ℝ (fderiv ℝ G) x z u := by
    rw [← fderiv_apply₂_const hDD x u w z, hH, fderiv_apply_const hGD x u z]
  have hnorm : ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ B + stepStabilityThreeCoefficient B * ‖v‖ ^ 2 := by
    exact (norm_second_tiltedAverage_le hf hgw hm v x hsmall).trans_eq (by
      dsimp only [stepStabilityThreeCoefficient]
      ring)
  change ‖fderiv ℝ (fderiv ℝ (fderiv ℝ T)) x z u w‖ ≤ _
  rw [heq]
  calc
    ‖fderiv ℝ (fderiv ℝ G) x z u‖ ≤ ‖fderiv ℝ (fderiv ℝ G) x z‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm _ u
    _ ≤ (‖fderiv ℝ (fderiv ℝ G) x‖ * ‖z‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ z) (norm_nonneg u)
    _ ≤ B + stepStabilityThreeCoefficient B * ‖v‖ ^ 2 := by
      rw [hz, hu, mul_one, mul_one]
      exact hnorm

theorem qPotential_three_step (hf : QPotential 3 B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QPotential 3 (B + stepStabilityThreeCoefficient B * ‖v‖ ^ 2) (vectorStep m v f) := by
  have hB : 0 ≤ B := hf.nonneg
  have hgain : 0 ≤ stepStabilityThreeCoefficient B * ‖v‖ ^ 2 := by
    dsimp only [stepStabilityThreeCoefficient]
    positivity
  refine ⟨by positivity, contDiff_step (r := 1) hf m v, ?_⟩
  intro j hj hjr x
  have hjcases : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hjcases with rfl | rfl | rfl
  · rw [norm_iteratedFDeriv_one]
    exact (norm_fderiv_step_le hf (by omega) m v x).trans (le_add_of_nonneg_right hgain)
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    apply (norm_second_step_le hf (by omega) hm.1 v x hsmall).trans
    dsimp only [stepStabilityThreeCoefficient]
    have hmono := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 2 * B ^ 2 * ‖v‖ ^ 2)
    nlinarith [mul_nonneg (pow_nonneg hB 3) (sq_nonneg ‖v‖)]
  · rw [← norm_iteratedFDeriv_fderiv (n := 2), ← norm_iteratedFDeriv_fderiv (n := 1),
      norm_iteratedFDeriv_one]
    exact norm_third_step_le hf hm v x hsmall

def tiltedCoarseCoefficient : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, B => tiltedCoarseCoefficient n B + (2 : ℝ) ^ n *
      (tiltedCoarseCoefficient n B + tiltedCoarseCoefficient n B ^ 2) * B

private theorem tiltedCoarseCoefficient_one_le (n : ℕ) (hB : 0 ≤ B) :
    1 ≤ tiltedCoarseCoefficient n B := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hM : 0 ≤ tiltedCoarseCoefficient n B := zero_le_one.trans ih
    dsimp only [tiltedCoarseCoefficient]
    nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
      (mul_nonneg (add_nonneg hM (sq_nonneg (tiltedCoarseCoefficient n B))) hB)]

theorem qBoundedJets_tiltedAverage_coarse (n : ℕ) (hf : QPotential r B f) (hr : 2 ≤ r)
    (hn : n ≤ r) (hg : QBoundedJets n C g) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E) :
    QBoundedJets n (tiltedCoarseCoefficient n B * C) (tiltedAverage m v f g) := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  induction n generalizing C g with
  | zero =>
    refine ⟨by simpa only [tiltedCoarseCoefficient, one_mul] using hC,
      tiltedAverage_smooth 0 hf hr hn hg m v, ?_⟩
    intro j hj x
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    simpa only [tiltedCoarseCoefficient, one_mul] using norm_tiltedAverage_le hf hr hg.norm_le m v x
  | succ n ih =>
    have hM : 0 ≤ tiltedCoarseCoefficient n B := zero_le_one.trans (tiltedCoarseCoefficient_one_le n hB)
    have hK : 0 ≤ tiltedCoarseCoefficient (n + 1) B * C :=
      mul_nonneg (zero_le_one.trans (tiltedCoarseCoefficient_one_le (n + 1) hB)) hC
    apply QBoundedJets.of_directional hK (tiltedAverage_smooth (n + 1) hf hr hn hg m v)
    · intro x
      have hbase := norm_tiltedAverage_le hf hr hg.norm_le m v x
      exact hbase.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (tiltedCoarseCoefficient_one_le (n + 1) hB) hC)
    · intro w hw
      have hgl : QBoundedJets n C g := hg.of_le (by omega)
      have hdg : QBoundedJets n C (fun y => fderiv ℝ g y w) := by
        simpa only [hw, mul_one] using hg.derivativeJets.apply_const w
      have hscore : QBoundedJets n B (fun y => fderiv ℝ f y w) := by
        simpa only [hw, mul_one] using (hf.of_le hn).derivativeJets.apply_const w
      have hG := ih (by omega) hgl hC
      have hS := ih (by omega) hscore hB
      have hP := ih (by omega) (hgl.mul hscore) (by positivity)
      have hD := ih (by omega) hdg hC
      have hCov := hP.sub (hG.mul hS)
      have hCov' : QBoundedJets n
          (tiltedCoarseCoefficient n B * ((2 : ℝ) ^ n * C * B) +
            (2 : ℝ) ^ n * (tiltedCoarseCoefficient n B * C) * (tiltedCoarseCoefficient n B * B))
          (spatialCovariance m v f g (fun y => fderiv ℝ f y w)) := hCov
      have hscaled := (hCov'.const_smul m).mono (mul_le_of_le_one_left hCov'.nonneg (by
        rw [abs_of_nonneg hm.1]
        exact hm.2))
      have hSum := hD.add hscaled
      have hFun : (fun y => fderiv ℝ (tiltedAverage m v f g) y w) = fun y =>
          tiltedAverage m v f (fun z => fderiv ℝ g z w) y +
            m * spatialCovariance m v f g (fun z => fderiv ℝ f z w) y := by
        funext y
        have hg1 := qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : 1 ≤ n + 1))
        have hs1 : QBddSmooth 1 B (fun y => fderiv ℝ f y w) := by
          simpa only [hw, mul_one] using (hf.of_le hr).directional w
        rw [fderiv_tiltedAverage_apply hf hr hg1, spatialCovariance_eq hf hr hg1 hs1]
        rfl
      rw [hFun]
      convert hSum using 1
      dsimp only [tiltedCoarseCoefficient]
      ring

def covarianceJetCoefficient : ℕ → ℝ → ℝ
  | 0, _ => 2
  | n + 1, B => covarianceJetCoefficient n B *
      (2 + (2 : ℝ) ^ (n + 1) * B * (1 + tiltedCoarseCoefficient n B))

private theorem covarianceJetCoefficient_two_le (n : ℕ) (hB : 0 ≤ B) :
    2 ≤ covarianceJetCoefficient n B := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hM : 0 ≤ tiltedCoarseCoefficient n B := zero_le_one.trans (tiltedCoarseCoefficient_one_le n hB)
    have hS : 0 ≤ covarianceJetCoefficient n B := by linarith
    dsimp only [covarianceJetCoefficient]
    have hprod : 0 ≤ (2 : ℝ) ^ (n + 1) * B * (1 + tiltedCoarseCoefficient n B) := by positivity
    nlinarith [mul_nonneg hS hprod]

theorem qBoundedJets_spatialCovariance (n : ℕ) (hf : QPotential r B f) (hr : 2 ≤ r)
    (hn : n + 1 ≤ r) (hg : QBoundedJets (n + 1) C g) (ha : QBoundedJets (n + 1) D a)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBoundedJets n (covarianceJetCoefficient n B * C * D * ‖v‖ ^ 2)
      (spatialCovariance m v f g a) := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hD : 0 ≤ D := ha.nonneg
  induction n generalizing C D g a with
  | zero =>
    have hg1 := qBoundedJets_iff_qBddSmooth.mp hg
    have ha1 := qBoundedJets_iff_qBddSmooth.mp ha
    refine ⟨by dsimp only [covarianceJetCoefficient]; positivity,
      (spatialCovariance_contDiff_one hf hr hg1 ha1 m v).of_le (by norm_num), ?_⟩
    intro j hj x
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, spatialCovariance_eq hf hr hg1 ha1]
    exact abs_test_covariance_le hf hr hg1 ha1 hm.1 v x hsmall
  | succ n ih =>
    have hS : 0 ≤ covarianceJetCoefficient (n + 1) B := by
      linarith [covarianceJetCoefficient_two_le (n + 1) hB]
    have hK : 0 ≤ covarianceJetCoefficient (n + 1) B * C * D * ‖v‖ ^ 2 := by positivity
    have hGl : QBoundedJets (n + 1) C g := hg.of_le (by omega)
    have hAl : QBoundedJets (n + 1) D a := ha.of_le (by omega)
    have hs : ContDiff ℝ (n + 1) (spatialCovariance m v f g a) :=
      (tiltedAverage_smooth (n + 1) hf hr (by omega) (hGl.mul hAl) m v).sub
        ((tiltedAverage_smooth (n + 1) hf hr (by omega) hGl m v).mul
          (tiltedAverage_smooth (n + 1) hf hr (by omega) hAl m v))
    apply QBoundedJets.of_directional hK hs
    · intro x
      have hg1 := qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : 1 ≤ n + 2))
      have ha1 := qBoundedJets_iff_qBddSmooth.mp (ha.of_le (by omega : 1 ≤ n + 2))
      rw [spatialCovariance_eq hf hr hg1 ha1]
      have hbase := abs_test_covariance_le hf hr hg1 ha1 hm.1 v x hsmall
      have hcoeff := mul_le_mul_of_nonneg_right (covarianceJetCoefficient_two_le (n + 1) hB)
        (by positivity : 0 ≤ C * D * ‖v‖ ^ 2)
      nlinarith
    · intro w hw
      have hdg : QBoundedJets (n + 1) C (fun y => fderiv ℝ g y w) := by
        simpa only [hw, mul_one] using hg.derivativeJets.apply_const w
      have hda : QBoundedJets (n + 1) D (fun y => fderiv ℝ a y w) := by
        simpa only [hw, mul_one] using ha.derivativeJets.apply_const w
      have hscore : QBoundedJets (n + 1) B (fun y => fderiv ℝ f y w) := by
        simpa only [hw, mul_one] using (hf.of_le hn).derivativeJets.apply_const w
      have h₁ := ih (by omega) hdg hAl hC hD
      have h₂ := ih (by omega) hGl hda hC hD
      have h₃ := ih (by omega) (hGl.mul hAl) hscore (by positivity) hB
      have h₄ := ih (by omega) hAl hscore hD hB
      have h₅ := ih (by omega) hGl hscore hC hB
      have hMG := qBoundedJets_tiltedAverage_coarse n hf hr (by omega) (hGl.of_le (by omega)) hm v
      have hMA := qBoundedJets_tiltedAverage_coarse n hf hr (by omega) (hAl.of_le (by omega)) hm v
      have scale (K : ℝ) (p : E → ℝ) (hp : QBoundedJets n K p) :
          QBoundedJets n K (fun y => m * p y) := by
        exact (hp.const_smul m).mono (mul_le_of_le_one_left hp.nonneg (by
          rw [abs_of_nonneg hm.1]
          exact hm.2))
      have hSum := (((h₁.add h₂).add (scale _ _ h₃)).sub
        (scale _ _ (hMG.mul h₄))).sub (scale _ _ (hMA.mul h₅))
      have hFun : (fun y => fderiv ℝ (spatialCovariance m v f g a) y w) = fun y =>
          spatialCovariance m v f (fun z => fderiv ℝ g z w) a y +
            spatialCovariance m v f g (fun z => fderiv ℝ a z w) y +
            m * spatialCovariance m v f (fun z => g z * a z) (fun z => fderiv ℝ f z w) y -
            m * (tiltedAverage m v f g y *
              spatialCovariance m v f a (fun z => fderiv ℝ f z w) y) -
            m * (tiltedAverage m v f a y *
              spatialCovariance m v f g (fun z => fderiv ℝ f z w) y) := by
        funext y
        let _ := stepLaw_probability hf hr m v y
        have hg2 := qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : 2 ≤ n + 2))
        have ha2 := qBoundedJets_iff_qBddSmooth.mp (ha.of_le (by omega : 2 ≤ n + 2))
        have hg1 := hg2.of_le (by omega : 1 ≤ 2)
        have ha1 := ha2.of_le (by omega : 1 ≤ 2)
        have hsc1 : QBddSmooth 1 B (fun z => fderiv ℝ f z w) := by
          simpa only [hw, mul_one] using (hf.of_le hr).directional w
        have hdg1 : QBddSmooth 1 C (fun z => fderiv ℝ g z w) := by
          simpa only [hw, mul_one] using hg2.potential.directional w
        have hda1 : QBddSmooth 1 D (fun z => fderiv ℝ a z w) := by
          simpa only [hw, mul_one] using ha2.potential.directional w
        have hp1 := qBoundedJets_iff_qBddSmooth.mp
          ((qBoundedJets_iff_qBddSmooth.mpr hg1).mul (qBoundedJets_iff_qBddSmooth.mpr ha1))
        rw [fderiv_spatialCovariance_apply hf hr hg2 ha2,
          covariance_product_centered (test_memLp hf hr hg1 m v y) (test_memLp hf hr ha1 m v y)
            (test_memLp hf hr hsc1 m v y) (test_memLp hf hr hp1 m v y)]
        simp only [Pi.mul_def]
        rw [← spatialCovariance_eq hf hr hdg1 ha1, ← spatialCovariance_eq hf hr hg1 hda1,
          ← spatialCovariance_eq hf hr hp1 hsc1, ← spatialCovariance_eq hf hr ha1 hsc1,
          ← spatialCovariance_eq hf hr hg1 hsc1]
        ring
      rw [hFun]
      convert hSum using 1
      dsimp only [covarianceJetCoefficient]
      simp only [pow_succ]
      ring

def tiltedStabilityCoefficient : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, B => tiltedStabilityCoefficient n B + covarianceJetCoefficient n B * B

private theorem tiltedStabilityCoefficient_nonneg (n : ℕ) (hB : 0 ≤ B) :
    0 ≤ tiltedStabilityCoefficient n B := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact add_nonneg ih (mul_nonneg (by linarith [covarianceJetCoefficient_two_le n hB]) hB)

theorem qBoundedJets_tiltedAverage (n : ℕ) (hf : QPotential r B f) (hr : 2 ≤ r)
    (hn : n + 1 ≤ r) (hg : QBoundedJets n C g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBoundedJets n (C + tiltedStabilityCoefficient n B * C * ‖v‖ ^ 2) (tiltedAverage m v f g) := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  induction n generalizing C g with
  | zero =>
    refine ⟨by simpa only [tiltedStabilityCoefficient, zero_mul, add_zero] using hC,
      tiltedAverage_smooth 0 hf hr (by omega) hg m v, ?_⟩
    intro j hj x
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    simpa only [tiltedStabilityCoefficient, zero_mul, add_zero] using
      norm_tiltedAverage_le hf hr hg.norm_le m v x
  | succ n ih =>
    have hH := tiltedStabilityCoefficient_nonneg (n + 1) hB
    have hK : 0 ≤ C + tiltedStabilityCoefficient (n + 1) B * C * ‖v‖ ^ 2 := by positivity
    apply QBoundedJets.of_directional hK (tiltedAverage_smooth (n + 1) hf hr (by omega) hg m v)
    · intro x
      exact (norm_tiltedAverage_le hf hr hg.norm_le m v x).trans (le_add_of_nonneg_right (by positivity))
    · intro w hw
      have hdg : QBoundedJets n C (fun y => fderiv ℝ g y w) := by
        simpa only [hw, mul_one] using hg.derivativeJets.apply_const w
      have hscore : QBoundedJets (n + 1) B (fun y => fderiv ℝ f y w) := by
        simpa only [hw, mul_one] using (hf.of_le hn).derivativeJets.apply_const w
      have hD := ih (by omega) hdg hC
      have hCov := qBoundedJets_spatialCovariance n hf hr (by omega) hg hscore hm v hsmall
      have hscaled := (hCov.const_smul m).mono (mul_le_of_le_one_left hCov.nonneg (by
        rw [abs_of_nonneg hm.1]
        exact hm.2))
      have hSum := hD.add hscaled
      have hFun : (fun y => fderiv ℝ (tiltedAverage m v f g) y w) = fun y =>
          tiltedAverage m v f (fun z => fderiv ℝ g z w) y +
            m * spatialCovariance m v f g (fun z => fderiv ℝ f z w) y := by
        funext y
        have hg1 := qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : 1 ≤ n + 1))
        have hs1 : QBddSmooth 1 B (fun y => fderiv ℝ f y w) := by
          simpa only [hw, mul_one] using (hf.of_le hr).directional w
        rw [fderiv_tiltedAverage_apply hf hr hg1, spatialCovariance_eq hf hr hg1 hs1]
        rfl
      rw [hFun]
      convert hSum using 1
      dsimp only [tiltedStabilityCoefficient]
      ring

theorem qbddSmooth_tiltedAverage (n : ℕ) (hf : QPotential r B f) (hr : 2 ≤ r)
    (hn : n + 1 ≤ r) (hg : QBddSmooth n C g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBddSmooth n (C + tiltedStabilityCoefficient n B * C * ‖v‖ ^ 2)
      (vectorStepAverage m v f g) := by
  exact qBoundedJets_iff_qBddSmooth.mp
    (qBoundedJets_tiltedAverage n hf hr hn (qBoundedJets_iff_qBddSmooth.mpr hg) hm v hsmall)

def stepStabilityCoefficient (r : ℕ) (B : ℝ) : ℝ := tiltedStabilityCoefficient (r - 1) B * B

private theorem potential_of_directional {n : ℕ} {K : ℝ} {f : E → ℝ}
    (hK : 0 ≤ K) (hf : ContDiff ℝ (n + 1) f)
    (hD : ∀ w : E, ‖w‖ = 1 → QBoundedJets n K (fun x => fderiv ℝ f x w)) :
    QPotential (n + 1) K f := by
  refine ⟨hK, hf, ?_⟩
  intro j hj hjn x
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  apply QBoundedJets.norm_succ_jet_le_of_directional (hf.of_le (by exact_mod_cast hjn)) hK x
  intro w hw
  exact (hD w hw).bound i (by omega) x

private theorem qPotential_step_succ (hf : QPotential (r + 2) B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QPotential (r + 2) (B + tiltedStabilityCoefficient (r + 1) B * B * ‖v‖ ^ 2) (vectorStep m v f) := by
  have hB : 0 ≤ B := hf.nonneg
  have hH := tiltedStabilityCoefficient_nonneg (r + 1) hB
  apply potential_of_directional (by positivity) (contDiff_step hf m v)
  intro w hw
  have hg : QBoundedJets (r + 1) B (fun y => fderiv ℝ f y w) := by
    simpa only [hw, mul_one] using hf.derivativeJets.apply_const w
  have h := qBoundedJets_tiltedAverage (r + 1) hf (by omega) le_rfl hg hm v hsmall
  have heq : (fun y => fderiv ℝ (vectorStep m v f) y w) =
      tiltedAverage m v f (fun y => fderiv ℝ f y w) := by
    funext y
    rw [fderiv_step_eq_tiltedAverage hf (by omega) m v,
      tiltedAverage_apply hf (by omega) hf.derivativeJets]
  rw [heq]
  exact h

theorem qPotential_step (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QPotential r (B + stepStabilityCoefficient r B * ‖v‖ ^ 2) (vectorStep m v f) := by
  have horder : (r - 2) + 2 = r := by omega
  have hcoeff : (r - 2) + 1 = r - 1 := by omega
  have hf' : QPotential ((r - 2) + 2) B f := by simpa only [horder] using hf
  have h := qPotential_step_succ hf' hm v hsmall
  simpa only [horder, hcoeff, stepStabilityCoefficient, mul_assoc] using h

private theorem tiltedCoarseCoefficient_mono (n : ℕ) (hB : 0 ≤ B) (hBC : B ≤ C) :
    tiltedCoarseCoefficient n B ≤ tiltedCoarseCoefficient n C := by
  have hC : 0 ≤ C := hB.trans hBC
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hMB : 0 ≤ tiltedCoarseCoefficient n B := zero_le_one.trans (tiltedCoarseCoefficient_one_le n hB)
    have hMC : 0 ≤ tiltedCoarseCoefficient n C := zero_le_one.trans (tiltedCoarseCoefficient_one_le n hC)
    dsimp only [tiltedCoarseCoefficient]
    gcongr

private theorem covarianceJetCoefficient_mono (n : ℕ) (hB : 0 ≤ B) (hBC : B ≤ C) :
    covarianceJetCoefficient n B ≤ covarianceJetCoefficient n C := by
  have hC : 0 ≤ C := hB.trans hBC
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hSB : 0 ≤ covarianceJetCoefficient n B := by linarith [covarianceJetCoefficient_two_le n hB]
    have hSC : 0 ≤ covarianceJetCoefficient n C := by linarith [covarianceJetCoefficient_two_le n hC]
    have hMB : 0 ≤ tiltedCoarseCoefficient n B := zero_le_one.trans (tiltedCoarseCoefficient_one_le n hB)
    have hMC : 0 ≤ tiltedCoarseCoefficient n C := zero_le_one.trans (tiltedCoarseCoefficient_one_le n hC)
    have hM := tiltedCoarseCoefficient_mono n hB hBC
    dsimp only [covarianceJetCoefficient]
    gcongr

private theorem tiltedStabilityCoefficient_mono (n : ℕ) (hB : 0 ≤ B) (hBC : B ≤ C) :
    tiltedStabilityCoefficient n B ≤ tiltedStabilityCoefficient n C := by
  have hC : 0 ≤ C := hB.trans hBC
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact add_le_add ih (mul_le_mul (covarianceJetCoefficient_mono n hB hBC) hBC hB
      (by linarith [covarianceJetCoefficient_two_le n hC]))

theorem stepStabilityCoefficient_nonneg (r : ℕ) (hB : 0 ≤ B) :
    0 ≤ stepStabilityCoefficient r B :=
  mul_nonneg (tiltedStabilityCoefficient_nonneg (r - 1) hB) hB

theorem stepStabilityCoefficient_mono (r : ℕ) (hB : 0 ≤ B) (hBC : B ≤ C) :
    stepStabilityCoefficient r B ≤ stepStabilityCoefficient r C := by
  exact mul_le_mul (tiltedStabilityCoefficient_mono (r - 1) hB hBC) hBC hB
    (tiltedStabilityCoefficient_nonneg (r - 1) (hB.trans hBC))

end StepCalculus
end SKBarriers2
