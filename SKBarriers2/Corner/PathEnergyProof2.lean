module

public import SKBarriers2.Corner.PathEnergyProof

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

private theorem defect_integrable_mul {μ : Measure ℝ} {a b : ℝ → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) : Integrable (fun t => a t*b t) μ := by
  exact (ha.integrable_mul hb).congr (ae_of_all μ (fun t => by simp only [Pi.mul_apply]))

private theorem defect_integrable_sub {μ : Measure ℝ} {a b : ℝ → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) : Integrable (fun t => a t-b t) μ := by
  exact (ha.sub hb).congr (ae_of_all μ (fun t => by simp only [Pi.sub_apply]))

private theorem defect_abs_three_add_le (a b c : ℝ) : |a+b+c| ≤ |a|+|b|+|c| := by
  exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

private theorem defect_line_derivative {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (v x : E) (t : ℝ) :
    HasDerivAt (fun a : ℝ => g (x+a • v)) (fderiv ℝ g (x+t • v) v) t := by
  have hl : HasDerivAt (fun a : ℝ => x+a • v) v t := by
    convert! ((hasDerivAt_id t).smul_const v).const_add x using 1
    simp only [one_smul]
  exact (hg.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hl

theorem spatial_quadratic_taylor_le {C : ℝ} {g : E → ℝ}
    (hg : QPotential 3 C g) (v x : E) (t : ℝ) :
    |g (x+t • v)-g x-fderiv ℝ g x v*t-directionalJet v 2 g x*t^2/2| ≤
      C*‖v‖^3*|t|^3 := by
  have h1 : QBddSmooth 2 (C*‖v‖) (directionalJet v 1 g) := by
    simpa only [Nat.zero_add,pow_one] using directionalJet_smooth (r := 2) 0 hg v
  have h2 : QBddSmooth 1 (C*‖v‖^2) (directionalJet v 2 g) :=
    directionalJet_smooth (r := 1) 1 hg v
  have hline : LipschitzWith ‖v‖₊ (fun t : ℝ => x+t • v) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm]
    have he : x+a • v-(x+b • v) = (a-b) • v := by module
    rw [he,norm_smul,Real.norm_eq_abs,Real.dist_eq,coe_nnnorm,mul_comm]
  have H := lipschitz_second_derivative_taylor
    (defect_line_derivative (hg.smooth.of_le (by norm_num)) v x)
    (defect_line_derivative (h1.smooth.of_le (by norm_num)) v x)
    ((h2.potential.lipschitzWith le_rfl).comp hline) 0 t
  simp only [zero_add,zero_smul,add_zero] at H
  exact H.trans_eq (by change (C*‖v‖^2)*‖v‖*|t|^3 = _; ring)

private theorem potential_increment_abs_le {C : ℝ} {g : E → ℝ}
    (hg : QPotential 3 C g) (v x : E) (t : ℝ) :
    |g (x+t • v)-g x| ≤ C*‖v‖*|t| := by
  have H := (hg.lipschitzWith (by norm_num)).dist_le_mul (x+t • v) x
  change dist (g (x+t • v)) (g x) ≤ C*dist (x+t • v) x at H
  simpa only [dist_eq_norm,Real.norm_eq_abs,add_sub_cancel_left,norm_smul,mul_comm,
    mul_left_comm,mul_assoc] using H

private theorem quadratic_product_remainder {C D d t g a g1 g2 a1 a2 : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (_hg : |g| ≤ C*d*|t|) (ha : |a| ≤ D*d*|t|)
    (hg1 : |g1| ≤ C*d) (hg2 : |g2| ≤ C*d^2)
    (_ha1 : |a1| ≤ D*d) (ha2 : |a2| ≤ D*d^2)
    (hRg : |g-g1*t-g2*t^2| ≤ C*d^3*|t|^3)
    (hRa : |a-a1*t-a2*t^2| ≤ D*d^3*|t|^3) :
    |g*a-g1*a1*t^2-(g1*a2+a1*g2)*t^3| ≤
      C*D*d^4*(3*|t|^4+|t|^5) := by
  have he : g*a-g1*a1*t^2-(g1*a2+a1*g2)*t^3 =
      (g-g1*t-g2*t^2)*a+g1*t*(a-a1*t-a2*t^2)+
        g2*t^2*(a-a1*t-a2*t^2)+g2*a2*t^4 := by ring
  have h1 : |(g-g1*t-g2*t^2)*a| ≤ C*D*d^4*|t|^4 := by
    rw [abs_mul]
    exact (mul_le_mul hRg ha (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have h2 : |g1*t*(a-a1*t-a2*t^2)| ≤ C*D*d^4*|t|^4 := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hg1 (abs_nonneg t)) hRa
      (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have h3 : |g2*t^2*(a-a1*t-a2*t^2)| ≤ C*D*d^4*|t|^5 := by
    rw [abs_mul,abs_mul,abs_pow]
    calc
      _ ≤ (C*d^2*|t|^2)*(D*d^3*|t|^3) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hg2 (by positivity)) hRa
          (abs_nonneg _) (by positivity)
      _ = (C*D*d^4*|t|^5)*d := by ring
      _ ≤ C*D*d^4*|t|^5 := mul_le_of_le_one_right (by positivity) hd1
  have h4 : |g2*a2*t^4| ≤ C*D*d^4*|t|^4 := by
    rw [abs_mul,abs_mul,abs_pow]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul hg2 ha2 (abs_nonneg _) (by positivity)) (by positivity)).trans_eq (by ring)
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)).trans
      ((add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by ring))

theorem centered_potential_product_taylor {C D : ℝ} {g a : E → ℝ}
    (hg : QPotential 3 C g) (ha : QPotential 3 D a)
    (v x : E) (hv : ‖v‖ ≤ 1) (t : ℝ) :
    |(g (x+t • v)-g x)*(a (x+t • v)-a x)-
      (fderiv ℝ g x v*fderiv ℝ a x v)*t^2-
      (fderiv ℝ g x v*(directionalJet v 2 a x/2)+
        fderiv ℝ a x v*(directionalJet v 2 g x/2))*t^3| ≤
      C*D*‖v‖^4*(3*|t|^4+|t|^5) := by
  have hd2 {B : ℝ} {f : E → ℝ} (hf : QPotential 3 B f) :
      |directionalJet v 2 f x/2| ≤ B*‖v‖^2 := by
    have H := (directionalJet_smooth (r := 0) 1 (hf.of_le (by norm_num : 2 ≤ 3)) v).abs_le x
    norm_num at H
    rw [abs_div]
    norm_num
    linarith [mul_nonneg hf.nonneg (sq_nonneg ‖v‖)]
  have H := quadratic_product_remainder hg.nonneg ha.nonneg (norm_nonneg v) hv
    (potential_increment_abs_le hg v x t) (potential_increment_abs_le ha v x t)
    (hg.directional_le (by norm_num) x v) (hd2 hg)
    (ha.directional_le (by norm_num) x v) (hd2 ha)
    (g := g (x+t • v)-g x) (a := a (x+t • v)-a x)
    (g1 := fderiv ℝ g x v) (a1 := fderiv ℝ a x v)
    (g2 := directionalJet v 2 g x/2) (a2 := directionalJet v 2 a x/2)
    (by simpa only [div_mul_eq_mul_div] using spatial_quadratic_taylor_le hg v x t)
    (by simpa only [div_mul_eq_mul_div] using spatial_quadratic_taylor_le ha v x t)
  exact H

def defectNoiseMomentBound (p : ℕ) (B : ℝ) : ℝ := |noiseAverageCoefficient 0 p B|

theorem noise_abs_moment_le {B : ℝ} {f : E → ℝ} (hf : QPotential 3 B f)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) (p : ℕ) :
    noiseMean m v f x (fun t => |t|^p) ≤ defectNoiseMomentBound p B := by
  have hc : ContDiff ℝ 0 (fun z : ℝ × E => |z.1|^p) := by
    apply contDiff_zero.mpr
    fun_prop
  have hj (t : ℝ) : QBoundedJets 0 (1*|t|^p) (fun _ : E => |t|^p) := by
    refine ⟨by positivity,contDiff_const,?_⟩
    intro j hj x
    have he : j = 0 := by omega
    subst j
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,abs_pow,abs_abs,one_mul,le_refl]
  have H := qBoundedJets_noiseMean_poly (g := fun (_ : E) t => |t|^p)
    (hf.of_le (by norm_num : 1 ≤ 3))
    (by norm_num : (0:ℝ) ≤ 1) p hc hj hm v hv
  have H' : |noiseMean m v f x (fun t => |t|^p)| ≤ noiseAverageCoefficient 0 p B := by
    simpa only [Real.norm_eq_abs,mul_one] using H.norm_le x
  exact (le_abs_self _).trans (H'.trans (le_abs_self _))

private theorem defect_potential_memLp {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QPotential 3 C g) (m : ℝ) (v x : E) :
    MemLp (fun t : ℝ => g (x+t • v)) 2 (stepLaw m v f x) := by
  have hc := hg.smooth.continuous.comp (vectorTranslation v).continuous
  have hG := (hg.boundedDerivs (by norm_num)).hasExpGrowth.compCLM (vectorTranslation v)
  have hI := (hG.mul hG).integrable_gaussianStepLaw
    ((hf.boundedDerivs (by norm_num)).compCLM (vectorTranslation v)) (hc.mul hc) m x
  rw [memLp_two_iff_integrable_sq]
  · change Integrable (fun t : ℝ => g (x+t • v)^2)
      (gaussianStepLaw m (fun z : E × ℝ => f (z.1+z.2 • v)) x)
    simpa only [pow_two,Function.comp_apply,vectorTranslation,add_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.smulRight_apply] using hI
  · exact (hg.smooth.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable

def potentialCovarianceDefectCoefficient (B : ℝ) : ℝ :=
  B+B^2+2*B*(3+B+B^2)+3*defectNoiseMomentBound 4 B+
    defectNoiseMomentBound 5 B+(1+B)^4

theorem potentialCovarianceDefectCoefficient_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ potentialCovarianceDefectCoefficient B := by
  dsimp only [potentialCovarianceDefectCoefficient,defectNoiseMomentBound]
  positivity

set_option maxHeartbeats 800000 in
theorem abs_potentialCovariance_sub_gradient_le {B C D : ℝ} {f g a : E → ℝ}
    (hf : QPotential 3 B f) (hg : QPotential 3 C g) (ha : QPotential 3 D a)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |spatialCovariance m v f g a x-fderiv ℝ g x v*fderiv ℝ a x v| ≤
      C*D*potentialCovarianceDefectCoefficient B*‖v‖^4 := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  let G : ℝ → ℝ := fun t => g (x+t • v)-g x
  let A : ℝ → ℝ := fun t => a (x+t • v)-a x
  let c2 := fderiv ℝ g x v*fderiv ℝ a x v
  let c3 := fderiv ℝ g x v*(directionalJet v 2 a x/2)+
    fderiv ℝ a x v*(directionalJet v 2 g x/2)
  let R : ℝ → ℝ := fun t => G t*A t-c2*t^2-c3*t^3
  have hB := hf.nonneg
  have hC := hg.nonneg
  have hD := ha.nonneg
  have hgm := defect_potential_memLp hf hg m v x
  have ham := defect_potential_memLp hf ha m v x
  have hG : MemLp G 2 μ := hgm.sub (memLp_const (g x))
  have hA : MemLp A 2 μ := ham.sub (memLp_const (a x))
  have hi (n : ℕ) : Integrable (fun t : ℝ => t^n) μ :=
    integrable_noise_pow hf (by norm_num) m v x n
  have hiabs (n : ℕ) : Integrable (fun t : ℝ => |t|^n) μ := by
    simpa only [Real.norm_eq_abs,abs_pow] using (hi n).norm
  have hR (t : ℝ) : |R t| ≤ C*D*‖v‖^4*(3*|t|^4+|t|^5) :=
    centered_potential_product_taylor hg ha v x hv t
  have hiMaj : Integrable (fun t : ℝ => C*D*‖v‖^4*(3*|t|^4+|t|^5)) μ :=
    (((hiabs 4).const_mul (3:ℝ)).add (hiabs 5)).const_mul (C*D*‖v‖^4)
  have hRE : |∫ t, R t ∂μ| ≤
      C*D*‖v‖^4*(3*defectNoiseMomentBound 4 B+defectNoiseMomentBound 5 B) := by
    calc
      _ ≤ ∫ t, |R t| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ t, C*D*‖v‖^4*(3*|t|^4+|t|^5) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ (fun t => abs_nonneg _))
          hiMaj (ae_of_all _ hR)
      _ = C*D*‖v‖^4*(3*noiseMean m v f x (fun t => |t|^4)+
          noiseMean m v f x (fun t => |t|^5)) := by
        rw [integral_const_mul,integral_add ((hiabs 4).const_mul 3) (hiabs 5),
          integral_const_mul]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (noise_abs_moment_le hf hm v x hv 4) (by norm_num))
        (noise_abs_moment_le hf hm v x hv 5)) (by positivity)
  have hc2 : |c2| ≤ C*D*‖v‖^2 := by
    dsimp only [c2]
    rw [abs_mul]
    exact (mul_le_mul (hg.directional_le (by norm_num) x v)
      (ha.directional_le (by norm_num) x v) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hjet {S : ℝ} {b : E → ℝ} (hb : QPotential 3 S b) :
      |directionalJet v 2 b x/2| ≤ S*‖v‖^2 := by
    have H := (directionalJet_smooth (r := 0) 1 (hb.of_le (by norm_num : 2 ≤ 3)) v).abs_le x
    norm_num at H
    rw [abs_div]
    norm_num
    linarith [mul_nonneg hb.nonneg (sq_nonneg ‖v‖)]
  have hc3 : |c3| ≤ 2*C*D*‖v‖^3 := by
    dsimp only [c3]
    calc
      _ ≤ |fderiv ℝ g x v*(directionalJet v 2 a x/2)|+
          |fderiv ℝ a x v*(directionalJet v 2 g x/2)| := abs_add_le _ _
      _ ≤ (C*‖v‖)*(D*‖v‖^2)+(D*‖v‖)*(C*‖v‖^2) := by
        rw [abs_mul,abs_mul]
        exact add_le_add
          (mul_le_mul (hg.directional_le (by norm_num) x v) (hjet ha) (abs_nonneg _) (by positivity))
          (mul_le_mul (ha.directional_le (by norm_num) x v) (hjet hg) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hM2 : |noiseMean m v f x (fun t => t^2)-1| ≤ (B+B^2)*‖v‖^2 := by
    have H := abs_noise_second_sub_one_le hf (by norm_num) m v x
    rw [abs_of_nonneg hm.1] at H
    have hm2 : m^2 ≤ 1 := by nlinarith [hm.1,hm.2]
    have hc : m*B+m^2*B^2 ≤ B+B^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hm.2 hB,
        mul_le_mul_of_nonneg_right hm2 (sq_nonneg B)]
    exact H.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  have hM3 := abs_noise_third_le hf (by norm_num) hm v x hv
  have hT2 : |c2*(noiseMean m v f x (fun t => t^2)-1)| ≤
      C*D*(B+B^2)*‖v‖^4 := by
    rw [abs_mul]
    exact (mul_le_mul hc2 hM2 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hT3 : |c3*noiseMean m v f x (fun t => t^3)| ≤
      C*D*(2*B*(3+B+B^2))*‖v‖^4 := by
    rw [abs_mul]
    exact (mul_le_mul hc3 hM3 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hEG : |∫ t, G t ∂μ| ≤ C*(1+B)^2*‖v‖^2 := by
    dsimp only [G]
    rw [integral_sub (hgm.integrable (by norm_num)) (integrable_const _),
      integral_const,probReal_univ,one_smul]
    exact abs_noiseMean_sub_le hf (by norm_num) hg (by norm_num) hm v x hv
  have hEA : |∫ t, A t ∂μ| ≤ D*(1+B)^2*‖v‖^2 := by
    dsimp only [A]
    rw [integral_sub (ham.integrable (by norm_num)) (integrable_const _),
      integral_const,probReal_univ,one_smul]
    exact abs_noiseMean_sub_le hf (by norm_num) ha (by norm_num) hm v x hv
  have hBias : |(∫ t, G t ∂μ)*(∫ t, A t ∂μ)| ≤ C*D*(1+B)^4*‖v‖^4 := by
    rw [abs_mul]
    exact (mul_le_mul hEG hEA (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hcenter : spatialCovariance m v f g a x =
      (∫ t, G t*A t ∂μ)-(∫ t, G t ∂μ)*(∫ t, A t ∂μ) := by
    have H := covariance_eq_sub hG hA
    dsimp only [G,A] at H
    rw [covariance_sub_const_left (hgm.integrable (by norm_num)),
      covariance_sub_const_right (ham.integrable (by norm_num))] at H
    simp only [Pi.mul_apply] at H
    have hbase : spatialCovariance m v f g a x =
        covariance (fun t : ℝ => g (x+t • v)) (fun t : ℝ => a (x+t • v)) μ := by
      simpa only [spatialCovariance,tiltedAverage,Pi.mul_apply] using
        (covariance_eq_sub hgm ham).symm
    exact hbase.trans H
  have hER : (∫ t, R t ∂μ) = (∫ t, G t*A t ∂μ)-
      c2*noiseMean m v f x (fun t => t^2)-c3*noiseMean m v f x (fun t => t^3) := by
    have hiProd : Integrable (fun t => G t*A t) μ := defect_integrable_mul hG hA
    have hiRest : Integrable (fun t => G t*A t-c2*t^2) μ :=
      defect_integrable_sub hiProd ((hi 2).const_mul c2)
    calc
      _ = (∫ t, G t*A t-c2*t^2 ∂μ)-(∫ t, c3*t^3 ∂μ) :=
        integral_sub hiRest ((hi 3).const_mul c3)
      _ = _ := by
        rw [integral_sub hiProd ((hi 2).const_mul c2),integral_const_mul,integral_const_mul]
        rfl
  have he : spatialCovariance m v f g a x-c2 =
      (∫ t, R t ∂μ)+c2*(noiseMean m v f x (fun t => t^2)-1)+
        c3*noiseMean m v f x (fun t => t^3)-(∫ t, G t ∂μ)*(∫ t, A t ∂μ) := by
    rw [hcenter,hER]
    ring
  change |spatialCovariance m v f g a x-c2| ≤ _
  rw [he]
  calc
    _ ≤ |∫ t, R t ∂μ|+|c2*(noiseMean m v f x (fun t => t^2)-1)|+
        |c3*noiseMean m v f x (fun t => t^3)|+|(∫ t, G t ∂μ)*(∫ t, A t ∂μ)| :=
      (abs_sub _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := (add_le_add (add_le_add (add_le_add hRE hT2) hT3) hBias).trans_eq (by
      dsimp only [potentialCovarianceDefectCoefficient]
      ring)

def stepTaylorDefect (m : ℝ) (v : E) (f : E → ℝ) (x : E) : ℝ :=
  vectorStep m v f x-(f x+m*(fderiv ℝ f x v)^2/2+directionalJet v 2 f x/2)

def massDefectSecondCoefficient (B a0 : ℝ) : ℝ :=
  (B^2*potentialCovarianceDefectCoefficient B+4*B*pathExpansionConstant B/a0)/a0

theorem abs_mass_defect_second_deriv_le {B a0 m : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ha0 : 0 < a0) (hm : m ∈ Icc a0 1)
    (v x : E) (hv : ‖v‖ ≤ 1) :
    |iteratedDeriv 2 (fun a : ℝ => vectorStep a v f x) m| ≤
      massDefectSecondCoefficient B a0*‖v‖^4 := by
  have hm0 : 0 < m := ha0.trans_le hm.1
  have hmcc : m ∈ Icc (0:ℝ) 1 := ⟨hm0.le,hm.2⟩
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  let d := fderiv ℝ f x v
  have hV := abs_potentialCovariance_sub_gradient_le hf3 hf3 hf3 hmcc v x hv
  have hS := abs_mass_deriv_remainder_le hf le_rfl ha0 hm v x hv
  have hmem := defect_potential_memLp hf3 hf3 m v x
  have hvar : variance (fun t : ℝ => f (x+t • v)) (stepLaw m v f x) =
      spatialCovariance m v f f f x := by
    rw [variance_eq_sub hmem]
    simp only [spatialCovariance,tiltedAverage,pow_two,Pi.mul_apply]
  rw [iteratedDeriv_succ,iteratedDeriv_one,second_mass_deriv_eq hf (by norm_num) hm0.ne',
    hvar,abs_div,abs_of_pos hm0]
  change |spatialCovariance m v f f f x-2*massSensitivity m v f x|/m ≤ _
  have he : spatialCovariance m v f f f x-2*massSensitivity m v f x =
      (spatialCovariance m v f f f x-d^2)-2*(massSensitivity m v f x-d^2/2) := by ring
  rw [he]
  have hB := hf.nonneg
  have hP := pathExpansionConstant_nonneg hB
  have hQ := potentialCovarianceDefectCoefficient_nonneg hB
  calc
    _ ≤ (|spatialCovariance m v f f f x-d^2|+
        2*|massSensitivity m v f x-d^2/2|)/m := by
      apply div_le_div_of_nonneg_right _ hm0.le
      have H := abs_sub (spatialCovariance m v f f f x-d^2)
        (2*(massSensitivity m v f x-d^2/2))
      simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using H
    _ ≤ (B^2*potentialCovarianceDefectCoefficient B*‖v‖^4+
        2*((2*B*pathExpansionConstant B/a0)*‖v‖^4))/m := by
      apply div_le_div_of_nonneg_right _ hm0.le
      exact add_le_add (by simpa only [d,pow_two,mul_assoc] using hV)
        (mul_le_mul_of_nonneg_left hS (by norm_num))
    _ ≤ (B^2*potentialCovarianceDefectCoefficient B*‖v‖^4+
        2*((2*B*pathExpansionConstant B/a0)*‖v‖^4))/a0 :=
      div_le_div_of_nonneg_left (by positivity) ha0 hm.1
    _ = _ := by dsimp only [massDefectSecondCoefficient]; ring

theorem massStepTaylorDefect_c2BoundAt {B a0 m : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ha0 : 0 < a0) (hm : m ∈ Icc a0 1)
    (v x : E) (hv : ‖v‖ ≤ 1) :
    Corner.C2BoundAt
      ((B*pathExpansionConstant B+2*B*pathExpansionConstant B/a0+
        massDefectSecondCoefficient B a0)*‖v‖^4)
      (fun a => stepTaylorDefect a v f x) m := by
  have hm0 : 0 < m := ha0.trans_le hm.1
  have hT : ContDiffAt ℝ 2 (fun a : ℝ => vectorStep a v f x) m :=
    contDiffAt_paramStep hf (by norm_num) contDiffAt_id contDiffAt_const hm0.ne' x
  let P : ℝ → ℝ := fun a => f x+a*(fderiv ℝ f x v)^2/2+directionalJet v 2 f x/2
  have hPc : ContDiff ℝ 2 P := by dsimp only [P]; fun_prop
  have hP1 (a : ℝ) : HasDerivAt P ((fderiv ℝ f x v)^2/2) a := by
    convert! ((((hasDerivAt_id a).mul_const ((fderiv ℝ f x v)^2)).div_const 2).const_add
      (f x)).add_const (directionalJet v 2 f x/2) using 1
    ring
  have hP2 : iteratedDeriv 2 P m = 0 := by
    rw [iteratedDeriv_succ,iteratedDeriv_one,
      show deriv P = fun _ => (fderiv ℝ f x v)^2/2 from funext (fun a => (hP1 a).deriv)]
    exact deriv_const m _
  have hB := hf.nonneg
  have hQ := potentialCovarianceDefectCoefficient_nonneg hB
  have hP := pathExpansionConstant_nonneg hB
  have hM : 0 ≤ massDefectSecondCoefficient B a0 := by
    dsimp only [massDefectSecondCoefficient]; positivity
  have h0 : 0 ≤ B*pathExpansionConstant B := by positivity
  have h1 : 0 ≤ 2*B*pathExpansionConstant B/a0 := by positivity
  refine ⟨by positivity,hT.sub hPc.contDiffAt,?_⟩
  intro c hc
  interval_cases c
  · have H := abs_step_generator_remainder_le hf le_rfl ⟨hm0.le,hm.2⟩ v x hv
    have he : stepTaylorDefect m v f x =
        vectorStep m v f x-f x-m*(fderiv ℝ f x v)^2/2-directionalJet v 2 f x/2 := by
      unfold stepTaylorDefect; ring
    rw [iteratedDeriv_zero,he]
    exact H.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · change |iteratedDeriv 1 (fun a => vectorStep a v f x-P a) m| ≤ _
    rw [iteratedDeriv_one,deriv_fun_sub (hT.differentiableAt (by norm_num))
      (hPc.differentiable (by norm_num) m),(hP1 m).deriv]
    exact (abs_mass_deriv_remainder_le hf le_rfl ha0 hm v x hv).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · change |iteratedDeriv 2 (fun a => vectorStep a v f x-P a) m| ≤ _
    rw [iteratedDeriv_fun_sub hT hPc.contDiffAt,hP2,sub_zero]
    exact (abs_mass_defect_second_deriv_le hf ha0 hm v x hv).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

private theorem defect_bounded_memLp {B C : ℝ} {f a : E → ℝ}
    (hf : QPotential 3 B f) (ha : QBoundedJets 2 C a) (m : ℝ) (v x : E) :
    MemLp (fun t : ℝ => a (x+t • v)) 2 (stepLaw m v f x) := by
  let _ := stepLaw_probability hf (by norm_num) m v x
  exact MemLp.of_bound (ha.smooth.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable C
      (ae_of_all _ (fun t => ha.norm_le _))

theorem abs_potential_bounded_covariance_le {B C D : ℝ} {f g a : E → ℝ}
    (hf : QPotential 3 B f) (hg : QPotential 3 C g) (ha : QBoundedJets 2 D a)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |spatialCovariance m v f g a x| ≤
      |potentialCovarianceCoefficient 0 B| *C*D*‖v‖^2 := by
  let _ := stepLaw_probability hf (by norm_num) m v x
  have H := qBoundedJets_potentialCovariance (n := 0)
    (hf.of_le (by norm_num)) (hg.of_le (by norm_num))
    (qBoundedJets_iff_qBddSmooth.mp ha).potential hm v hv
  have hgm := defect_potential_memLp hf hg m v x
  have ham := defect_bounded_memLp hf ha m v x
  have he : spatialCovariance m v f g a x =
      covariance (fun t : ℝ => g (x+t • v)) (fun t : ℝ => a (x+t • v)) (stepLaw m v f x) :=
    by simpa only [spatialCovariance,tiltedAverage,Pi.mul_apply] using
      (covariance_eq_sub hgm ham).symm
  rw [he]
  have hbound : |covariance (fun t : ℝ => g (x+t • v))
      (fun t : ℝ => a (x+t • v)) (stepLaw m v f x)| ≤
      potentialCovarianceCoefficient 0 B*C*D*‖v‖^2 := by
    simpa only [Real.norm_eq_abs] using H.norm_le x
  exact hbound.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hg.nonneg) ha.nonneg) (sq_nonneg _))

private theorem defect_growth_line {g : E → ℝ} (hg : HasExpGrowth g) (x v : E) :
    HasExpGrowth (fun t : ℝ => g (x+t • v)) := by
  obtain ⟨C,M,hC,hM,hbound⟩ := hg
  refine ⟨C*Real.exp (M*‖x‖),M*‖v‖,by positivity,by positivity,?_⟩
  intro t
  apply (hbound (x+t • v)).trans
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ M*(‖x‖+‖t • v‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hM
    _ = _ := by rw [norm_smul]; ring

set_option maxHeartbeats 800000 in
theorem covariance_noisy_direction_eq {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 4 B f) (hg : QPotential 3 C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v w x : E) :
    covariance (fun t : ℝ => g (x+t • v))
        (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) (stepLaw m v f x) =
      spatialCovariance m v f g (directionSource m v w f) x+
        tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x := by
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  let P : ℝ → ℝ := fun t => g (x+t • v)*fderiv ℝ f (x+t • v) w
  let Q : ℝ → ℝ := fun t => fderiv ℝ g (x+t • v) v*fderiv ℝ f (x+t • v) w+
    g (x+t • v)*fderiv ℝ (fderiv ℝ f) (x+t • v) v w
  have hW := (hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w
  have hV := (hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const v
  have hH := (hf.derivativeJets.derivativeJets.apply_const v).apply_const w
  have hG := hg.derivativeJets.apply_const v
  have hJ := qBoundedJets_directionSource hf hm v w
  have hline : Continuous (fun t : ℝ => x+t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdW (t : ℝ) : HasDerivAt (fun a : ℝ => fderiv ℝ f (x+a • v) w)
      (fderiv ℝ (fderiv ℝ f) (x+t • v) v w) t := by
    have hl : HasDerivAt (fun a : ℝ => x+a • v) v t := by
      convert! ((hasDerivAt_id t).smul_const v).const_add x using 1
      simp only [one_smul]
    have H := (((hf.smooth.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (x+t • v)).hasFDerivAt.comp_hasDerivAt t hl).clm_apply
        (hasDerivAt_const t w)
    simpa only [Function.comp_def,map_zero,add_zero] using H
  have hd (t : ℝ) : HasDerivAt P (Q t) t :=
    (defect_line_derivative (hg.smooth.of_le (by norm_num)) v x t).mul (hdW t)
  have hgc : Continuous (fun t : ℝ => g (x+t • v)) := hg.smooth.continuous.comp hline
  have hgg : HasExpGrowth (fun t : ℝ => g (x+t • v)) :=
    defect_growth_line (hg.boundedDerivs (by norm_num)).hasExpGrowth x v
  have hgW : HasExpGrowth (fun t : ℝ => fderiv ℝ f (x+t • v) w) :=
    HasExpGrowth.of_bounded hW.nonneg (fun t => hW.norm_le _)
  have hgH : HasExpGrowth (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x+t • v) v w) :=
    HasExpGrowth.of_bounded hH.nonneg (fun t => hH.norm_le _)
  have hgG : HasExpGrowth (fun t : ℝ => fderiv ℝ g (x+t • v) v) :=
    HasExpGrowth.of_bounded hG.nonneg (fun t => hG.norm_le _)
  have hcQ : Continuous Q := ((hG.smooth.continuous.comp hline).mul
    (hW.smooth.continuous.comp hline)).add (hgc.mul (hH.smooth.continuous.comp hline))
  have hgQ : HasExpGrowth Q := (hgG.mul hgW).add (hgg.mul hgH)
  have H := tilted_integration_by_parts hf (by norm_num) m v x hd hcQ (hgg.mul hgW) hgQ
  have hgm := defect_potential_memLp hf3 hg m v x
  have hJm := defect_bounded_memLp hf3 hJ m v x
  have hHm := defect_bounded_memLp hf3 hH m v x
  have hGW := hG.mul hW
  have hWV := hW.mul hV
  have hGWm := defect_bounded_memLp hf3 hGW m v x
  have hWVm := defect_bounded_memLp hf3 hWV m v x
  have hiQ : Integrable Q μ := (hGWm.integrable (by norm_num)).add (hgm.integrable_mul hHm)
  have hiProd := defect_integrable_mul hgm hWVm
  have hpoint (t : ℝ) : Q t+m*(P t*fderiv ℝ f (x+t • v) v) =
      fderiv ℝ g (x+t • v) v*fderiv ℝ f (x+t • v) w+
        g (x+t • v)*directionSource m v w f (x+t • v) := by
    dsimp only [P,Q,directionSource]
    ring
  have hcombine : noiseMean m v f x Q+
      m*noiseMean m v f x (fun t => P t*fderiv ℝ f (x+t • v) v) =
      tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x+
        tiltedAverage m v f (fun y => g y*directionSource m v w f y) x := by
    unfold noiseMean tiltedAverage
    rw [← integral_const_mul,← integral_add hiQ (by
      convert hiProd.const_mul m using 1
      funext t; dsimp only [P]; ring)]
    simp_rw [hpoint]
    rw [integral_add (hGWm.integrable (by norm_num)) (defect_integrable_mul hgm hJm)]
  rw [hcombine] at H
  have hNm : MemLp (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) 2 μ :=
    memLp_noise_of_growth hf3 m v x (continuous_id.mul (hW.smooth.continuous.comp hline))
      ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).mul hgW)
  rw [covariance_eq_sub hgm hNm]
  simp only [Pi.mul_apply]
  have hprod : (∫ t, g (x+t • v)*(t*fderiv ℝ f (x+t • v) w) ∂μ) =
      noiseMean m v f x (fun t => t*P t) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by dsimp only [P]; ring)
  rw [hprod,H]
  have hmean := noise_directionSource hf (by norm_num) m v w x
  change noiseMean m v f x (fun t => t*fderiv ℝ f (x+t • v) w) =
    tiltedAverage m v f (directionSource m v w f) x at hmean
  change _ - (tiltedAverage m v f g x)*
    noiseMean m v f x (fun t => t*fderiv ℝ f (x+t • v) w) = _
  rw [hmean]
  unfold spatialCovariance
  ring

def mixedDirectionCovarianceDefectCoefficient (B : ℝ) : ℝ :=
  |potentialCovarianceCoefficient 0 B| *(B+4*B^2)+4*B*(1+B)^2

theorem abs_covariance_noisy_direction_sub_gradient_le {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 4 B f) (hg : QPotential 3 C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v w x : E) (hv : ‖v‖ ≤ 1) :
    |covariance (fun t : ℝ => g (x+t • v))
        (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) (stepLaw m v f x)-
      fderiv ℝ g x v*fderiv ℝ f x w| ≤
      C*mixedDirectionCovarianceDefectCoefficient B*‖v‖^3*‖w‖ := by
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hJ : QBoundedJets 2 ((B+4*B^2)*‖v‖*‖w‖) (directionSource m v w f) := by
    simpa only [show (2:ℝ)^2 = 4 from by norm_num] using qBoundedJets_directionSource hf hm v w
  have hCov := abs_potential_bounded_covariance_le hf3 hg hJ hm v x hv
  have hW := (hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w
  have hG := hg.derivativeJets.apply_const v
  have hprod : QBoundedJets 2 (4*(C*‖v‖)*(B*‖w‖))
      (fun y => fderiv ℝ g y v*fderiv ℝ f y w) := by
    simpa only [show (2:ℝ)^2 = 4 from by norm_num] using hG.mul hW
  have hBias := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hprod).potential (by norm_num) hm v x hv
  rw [covariance_noisy_direction_eq hf hg hm]
  have he : spatialCovariance m v f g (directionSource m v w f) x+
      tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x-
      fderiv ℝ g x v*fderiv ℝ f x w =
      spatialCovariance m v f g (directionSource m v w f) x+
        (tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x-
          fderiv ℝ g x v*fderiv ℝ f x w) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hCov hBias).trans_eq (by
    dsimp only [mixedDirectionCovarianceDefectCoefficient]
    ring))

def secondNoiseBiasCoefficient (B : ℝ) : ℝ :=
  defectNoiseMomentBound 4 B+B*(3+B+B^2)+B+B^2

theorem abs_noise_second_weighted_sub_le {B C : ℝ} {f a : E → ℝ}
    (hf : QPotential 3 B f) (ha : QBoundedJets 2 C a)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |noiseMean m v f x (fun t => t^2*a (x+t • v))-a x| ≤
      C*secondNoiseBiasCoefficient B*‖v‖^2 := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  let R : ℝ → ℝ := fun t => t^2*a (x+t • v)-a x*t^2-fderiv ℝ a x v*t^3
  have hap := (qBoundedJets_iff_qBddSmooth.mp ha).potential
  have hB := hf.nonneg
  have hC := ha.nonneg
  have hmem := defect_bounded_memLp hf ha m v x
  have hpow (n : ℕ) : MemLp (fun t : ℝ => t^n) 2 μ :=
    memLp_noise_of_growth hf m v x (continuous_id.pow n)
      ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).pow n)
  have hi (n : ℕ) : Integrable (fun t : ℝ => t^n) μ :=
    (hpow n).integrable (by norm_num)
  have hR (t : ℝ) : |R t| ≤ C*‖v‖^2*t^4 := by
    have H := hap.taylor_linear_remainder_le le_rfl x (t • v)
    have he : R t = t^2*(a (x+t • v)-a x-fderiv ℝ a x (t • v)) := by
      dsimp only [R]
      rw [map_smul,smul_eq_mul]
      ring
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg t)]
    apply (mul_le_mul_of_nonneg_left H (sq_nonneg t)).trans_eq
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hRE : |∫ t, R t ∂μ| ≤ C*‖v‖^2*defectNoiseMomentBound 4 B := by
    calc
      _ ≤ ∫ t, |R t| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ t, C*‖v‖^2*t^4 ∂μ := integral_mono_of_nonneg
        (ae_of_all μ (fun t => abs_nonneg _)) ((hi 4).const_mul (C*‖v‖^2))
        (ae_of_all μ hR)
      _ = C*‖v‖^2*noiseMean m v f x (fun t => |t|^4) := by
        rw [integral_const_mul]
        simp only [Even.pow_abs (by norm_num : Even 4)]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (noise_abs_moment_le hf hm v x hv 4) (by positivity)
  have hM2 : |noiseMean m v f x (fun t => t^2)-1| ≤ (B+B^2)*‖v‖^2 := by
    have H := abs_noise_second_sub_one_le hf (by norm_num) m v x
    rw [abs_of_nonneg hm.1] at H
    have hm2 : m^2 ≤ 1 := by nlinarith [hm.1,hm.2]
    apply H.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hm.2 hB,
      mul_le_mul_of_nonneg_right hm2 (sq_nonneg B)]
  have hM3 := abs_noise_third_le hf (by norm_num) hm v x hv
  have hA : |a x| ≤ C := by simpa only [Real.norm_eq_abs] using ha.norm_le x
  have hD := hap.directional_le (by norm_num) x v
  have hT2 : |a x*(noiseMean m v f x (fun t => t^2)-1)| ≤ C*(B+B^2)*‖v‖^2 := by
    rw [abs_mul]
    exact (mul_le_mul hA hM2 (abs_nonneg _) hC).trans_eq (by ring)
  have hT3 : |fderiv ℝ a x v*noiseMean m v f x (fun t => t^3)| ≤
      C*(B*(3+B+B^2))*‖v‖^2 := by
    rw [abs_mul]
    exact (mul_le_mul hD hM3 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hER : (∫ t, R t ∂μ) = noiseMean m v f x (fun t => t^2*a (x+t • v))-
      a x*noiseMean m v f x (fun t => t^2)-
        fderiv ℝ a x v*noiseMean m v f x (fun t => t^3) := by
    have hiProd := defect_integrable_mul (hpow 2) hmem
    have hiRest := defect_integrable_sub hiProd ((hi 2).const_mul (a x))
    calc
      _ = (∫ t, t^2*a (x+t • v)-a x*t^2 ∂μ)-
          (∫ t, fderiv ℝ a x v*t^3 ∂μ) := integral_sub hiRest ((hi 3).const_mul _)
      _ = _ := by
        rw [integral_sub hiProd ((hi 2).const_mul (a x)),integral_const_mul,integral_const_mul]
        rfl
  have he : noiseMean m v f x (fun t => t^2*a (x+t • v))-a x =
      (∫ t, R t ∂μ)+a x*(noiseMean m v f x (fun t => t^2)-1)+
        fderiv ℝ a x v*noiseMean m v f x (fun t => t^3) := by
    rw [hER]; ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hRE hT2) hT3).trans_eq (by
      dsimp only [secondNoiseBiasCoefficient]; ring))

def noisyDirectionVarianceDefectCoefficient (B : ℝ) : ℝ :=
  4*B^2*secondNoiseBiasCoefficient B+(B+4*B^2)^2

theorem abs_noisy_direction_variance_sub_le {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (v w x : E) (hv : ‖v‖ ≤ 1) :
    |variance (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) (stepLaw m v f x)-
      (fderiv ℝ f x w)^2| ≤
      noisyDirectionVarianceDefectCoefficient B*‖v‖^2*‖w‖^2 := by
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hW := (hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w
  have hWsq : QBoundedJets 2 (4*B^2*‖w‖^2) (fun y => (fderiv ℝ f y w)^2) := by
    convert hW.mul hW using 1
    · norm_num; ring
    · funext y; ring
  have hJ : QBoundedJets 2 ((B+4*B^2)*‖v‖*‖w‖) (directionSource m v w f) := by
    simpa only [show (2:ℝ)^2 = 4 from by norm_num] using qBoundedJets_directionSource hf hm v w
  have hmean : |noiseMean m v f x (fun t => t*fderiv ℝ f (x+t • v) w)| ≤
      (B+4*B^2)*‖v‖*‖w‖ := by
    rw [noise_directionSource hf (by norm_num)]
    exact abs_noiseMean_le hf (by norm_num) m v x (fun t => by
      simpa only [Real.norm_eq_abs] using hJ.norm_le (x+t • v))
  have hmeanSq : (noiseMean m v f x (fun t => t*fderiv ℝ f (x+t • v) w))^2 ≤
      (B+4*B^2)^2*‖v‖^2*‖w‖^2 := by
    have H := pow_le_pow_left₀ (abs_nonneg _) hmean 2
    simpa only [sq_abs,mul_pow] using H
  have hmem : MemLp (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) 2 (stepLaw m v f x) :=
    memLp_noise_of_growth hf3 m v x
      (continuous_id.mul (hW.smooth.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))))
      ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).mul
        (HasExpGrowth.of_bounded hW.nonneg (fun t => hW.norm_le _)))
  have hBias := abs_noise_second_weighted_sub_le hf3 hWsq hm v x hv
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply]
  have he : (∫ t : ℝ, (t*fderiv ℝ f (x+t • v) w)^2 ∂stepLaw m v f x)-
      (∫ t : ℝ, t*fderiv ℝ f (x+t • v) w ∂stepLaw m v f x)^2-
      (fderiv ℝ f x w)^2 =
      (noiseMean m v f x (fun t => t^2*(fderiv ℝ f (x+t • v) w)^2)-
        (fderiv ℝ f x w)^2)-
        (noiseMean m v f x (fun t => t*fderiv ℝ f (x+t • v) w))^2 := by
    simp only [mul_pow,noiseMean]; ring
  rw [he]
  have hmeanAbs : |(noiseMean m v f x (fun t => t*fderiv ℝ f (x+t • v) w))^2| ≤
      (B+4*B^2)^2*‖v‖^2*‖w‖^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hmeanSq
  exact (abs_sub _ _).trans ((add_le_add hBias
    hmeanAbs).trans_eq (by
      dsimp only [noisyDirectionVarianceDefectCoefficient]; ring))

private theorem defect_fderiv_add_smul {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QPotential 3 C g) (η : ℝ) :
    fderiv ℝ (fun y => g y+η*f y) = fun y => fderiv ℝ g y+η • fderiv ℝ f y := by
  funext y
  rw [fderiv_fun_add (hg.smooth.differentiable (by norm_num) y)
      ((hf.smooth.differentiable (by norm_num) y).const_mul η),
    fderiv_const_mul (hf.smooth.differentiable (by norm_num) y)]

private theorem defect_potential_add_smul {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QPotential 3 C g) (η : ℝ) :
    QPotential 3 (C+|η| *B) (fun y => g y+η*f y) := by
  have hsum := hg.derivativeJets.add (hf.derivativeJets.const_smul η)
  refine ⟨by positivity [hf.nonneg,hg.nonneg],
    hg.smooth.add (contDiff_const.mul hf.smooth),?_⟩
  intro j hj hj3 y
  cases j with
  | zero => omega
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv,defect_fderiv_add_smul hf hg η]
    exact hsum.bound j (by omega) y

theorem abs_secondScoreVariance_sub_quadratic_le {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 4 B f) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (η : ℝ) (v w x : E) (hv : ‖v‖ ≤ 1) :
    |secondScoreVariance m η v w f g x-
      (fderiv ℝ g x v+η*fderiv ℝ f x v+fderiv ℝ f x w)^2| ≤
      (C+|η| *B)^2*potentialCovarianceDefectCoefficient B*‖v‖^4+
        2*(C+|η| *B)*mixedDirectionCovarianceDefectCoefficient B*‖v‖^3*‖w‖+
        noisyDirectionVarianceDefectCoefficient B*‖v‖^2*‖w‖^2 := by
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hg3 := (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 3 ≤ 4))).potential
  let H : E → ℝ := fun y => g y+η*f y
  have hH : QPotential 3 (C+|η| *B) H := defect_potential_add_smul hf3 hg3 η
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hHm := defect_potential_memLp hf3 hH m v x
  have hW := (hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w
  have hYm : MemLp (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) 2 μ :=
    memLp_noise_of_growth hf3 m v x
      (continuous_id.mul (hW.smooth.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))))
      ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).mul
        (HasExpGrowth.of_bounded hW.nonneg (fun t => hW.norm_le _)))
  have hdH : fderiv ℝ H x v = fderiv ℝ g x v+η*fderiv ℝ f x v := by
    rw [defect_fderiv_add_smul hf3 hg3 η]
    simp only [add_apply,smul_apply,smul_eq_mul]
  have hVarH : variance (fun t : ℝ => H (x+t • v)) μ =
      spatialCovariance m v f H H x := by
    rw [variance_eq_sub hHm]
    simp only [spatialCovariance,tiltedAverage,pow_two,Pi.mul_apply]
  have h0 := abs_potentialCovariance_sub_gradient_le hf3 hH hH hm v x hv
  have h1 := abs_covariance_noisy_direction_sub_gradient_le hf hH hm v w x hv
  have h2 := abs_noisy_direction_variance_sub_le hf hm v w x hv
  rw [secondScoreVariance_eq_variance hf3 (hg.of_le (by norm_num : 3 ≤ 4))]
  change |variance (fun t : ℝ => H (x+t • v)+t*fderiv ℝ f (x+t • v) w) μ-
    (fderiv ℝ g x v+η*fderiv ℝ f x v+fderiv ℝ f x w)^2| ≤ _
  rw [variance_fun_add hHm hYm,hVarH,← hdH]
  have he : spatialCovariance m v f H H x+
      2*covariance (fun t : ℝ => H (x+t • v))
        (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ+
      variance (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ-
      (fderiv ℝ H x v+fderiv ℝ f x w)^2 =
      (spatialCovariance m v f H H x-fderiv ℝ H x v*fderiv ℝ H x v)+
      2*(covariance (fun t : ℝ => H (x+t • v))
        (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ-fderiv ℝ H x v*fderiv ℝ f x w)+
      (variance (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ-(fderiv ℝ f x w)^2) := by ring
  rw [he]
  have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
  calc
    _ ≤ |spatialCovariance m v f H H x-fderiv ℝ H x v*fderiv ℝ H x v|+
        2*|covariance (fun t : ℝ => H (x+t • v))
          (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ-fderiv ℝ H x v*fderiv ℝ f x w|+
        |variance (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ-(fderiv ℝ f x w)^2| := by
      have H := defect_abs_three_add_le
        (spatialCovariance m v f H H x-fderiv ℝ H x v*fderiv ℝ H x v)
        (2*(covariance (fun t : ℝ => H (x+t • v))
          (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ-fderiv ℝ H x v*fderiv ℝ f x w))
        (variance (fun t : ℝ => t*fderiv ℝ f (x+t • v) w) μ-(fderiv ℝ f x w)^2)
      simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using H
    _ ≤ _ := (add_le_add (add_le_add h0 h1') h2).trans_eq (by ring)

def stepQuadraticSecondSource (m : ℝ) (v : E) (f g q : E → ℝ)
    (dm ddm : ℝ) (w b : E) (x : E) : ℝ :=
  q x+m*fderiv ℝ f x v*fderiv ℝ q x v+directionalJet v 2 q x/2+
    2*mixedDirectionSource m v w f g x+
    fderiv ℝ (fderiv ℝ f) x w w+directionSource m v b f x+
    m*(fderiv ℝ g x v+fderiv ℝ f x w)^2+
    2*dm*fderiv ℝ f x v*(fderiv ℝ g x v+fderiv ℝ f x w)+
    ddm*(fderiv ℝ f x v)^2/2

def mixedStepDefectSecondBound (B A H a0 m dm ddm : ℝ) (v w b : E) : ℝ :=
  (H*pathExpansionConstant B+(A+|dm/m| *B)^2*potentialCovarianceDefectCoefficient B+
      |ddm-2*dm^2/m| *(2*B*pathExpansionConstant B/a0))*‖v‖^4+
    (2*(1+4*B)*A*(1+B)^2+
      2*(A+|dm/m| *B)*mixedDirectionCovarianceDefectCoefficient B)*‖v‖^3*‖w‖+
    (B*secondNoiseBiasCoefficient B+noisyDirectionVarianceDefectCoefficient B)*‖v‖^2*‖w‖^2+
    (B+4*B^2)*(1+B)^2*‖v‖^3*‖b‖

private theorem defect_abs_six_add_le (a b c d e f : ℝ) :
    |a+b+c+d+e+f| ≤ |a|+|b|+|c|+|d|+|e|+|f| := by
  have H := Finset.abs_sum_le_sum_abs (fun i : Fin 6 => ![a,b,c,d,e,f] i) Finset.univ
  simpa only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero,add_assoc] using H

set_option maxHeartbeats 800000 in
theorem abs_secondVariationStep_sub_quadratic_le {B A H a0 m : ℝ}
    {f g q : E → ℝ} (hf : QPotential 4 B f)
    (hg : QBoundedJets 4 A g) (hq : QBoundedJets 4 H q)
    (ha0 : 0 < a0) (hm : m ∈ Icc a0 1)
    (dm ddm : ℝ) (v w b x : E) (hv : ‖v‖ ≤ 1) :
    |secondVariationStep m v f g q dm ddm w b x-
      stepQuadraticSecondSource m v f g q dm ddm w b x| ≤
      mixedStepDefectSecondBound B A H a0 m dm ddm v w b := by
  have hm0 : 0 < m := ha0.trans_le hm.1
  have hmcc : m ∈ Icc (0:ℝ) 1 := ⟨hm0.le,hm.2⟩
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hqt := abs_noiseMean_generator_remainder_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hq).potential (by norm_num) hmcc v x hv
  have hMix : QBoundedJets 2 ((1+4*B)*A*‖v‖*‖w‖) (mixedDirectionSource m v w f g) := by
    simpa only [show (2:ℝ)^2 = 4 from by norm_num] using
      qBoundedJets_mixedDirectionSource_order (n := 1) hf hg hmcc v w
  have hMixBias := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hMix).potential (by norm_num) hmcc v x hv
  have hMix2 : |2*(tiltedAverage m v f (mixedDirectionSource m v w f g) x-
      mixedDirectionSource m v w f g x)| ≤
      2*((1+4*B)*A*‖v‖*‖w‖*(1+B)^2*‖v‖^2) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hMixBias (by norm_num)
  have hHess : QBoundedJets 2 (B*‖w‖^2)
      (fun y => fderiv ℝ (fderiv ℝ f) y w w) := by
    convert (hf.derivativeJets.derivativeJets.apply_const w).apply_const w using 1
    ring
  have hHessBias := abs_noise_second_weighted_sub_le hf3 hHess hmcc v x hv
  have hDir : QBoundedJets 2 ((B+4*B^2)*‖v‖*‖b‖) (directionSource m v b f) := by
    simpa only [show (2:ℝ)^2 = 4 from by norm_num] using qBoundedJets_directionSource hf hmcc v b
  have hDirBias := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hDir).potential (by norm_num) hmcc v x hv
  have hScore := abs_secondScoreVariance_sub_quadratic_le hf hg hmcc (dm/m) v w x hv
  have hScoreScaled : |m*(secondScoreVariance m (dm/m) v w f g x-
      (fderiv ℝ g x v+(dm/m)*fderiv ℝ f x v+fderiv ℝ f x w)^2)| ≤
      (A+|dm/m| *B)^2*potentialCovarianceDefectCoefficient B*‖v‖^4+
        2*(A+|dm/m| *B)*mixedDirectionCovarianceDefectCoefficient B*‖v‖^3*‖w‖+
        noisyDirectionVarianceDefectCoefficient B*‖v‖^2*‖w‖^2 := by
    rw [abs_mul,abs_of_pos hm0]
    exact (mul_le_mul_of_nonneg_left hScore hm0.le).trans
      (mul_le_of_le_one_left ((abs_nonneg _).trans hScore) hm.2)
  have hMass := abs_mass_deriv_remainder_le hf le_rfl ha0 hm v x hv
  have hMassScaled : |(ddm-2*dm^2/m)*(massSensitivity m v f x-(fderiv ℝ f x v)^2/2)| ≤
      |ddm-2*dm^2/m| *((2*B*pathExpansionConstant B/a0)*‖v‖^4) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hMass (abs_nonneg _)
  have he : secondVariationStep m v f g q dm ddm w b x-
      stepQuadraticSecondSource m v f g q dm ddm w b x =
      (tiltedAverage m v f q x-q x-m*fderiv ℝ f x v*fderiv ℝ q x v-directionalJet v 2 q x/2)+
      2*(tiltedAverage m v f (mixedDirectionSource m v w f g) x-mixedDirectionSource m v w f g x)+
      (noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ f) (x+t • v) w w)-
        fderiv ℝ (fderiv ℝ f) x w w)+
      (tiltedAverage m v f (directionSource m v b f) x-directionSource m v b f x)+
      m*(secondScoreVariance m (dm/m) v w f g x-
        (fderiv ℝ g x v+(dm/m)*fderiv ℝ f x v+fderiv ℝ f x w)^2)+
      (ddm-2*dm^2/m)*(massSensitivity m v f x-(fderiv ℝ f x v)^2/2) := by
    unfold secondVariationStep stepQuadraticSecondSource
    field_simp [hm0.ne']
    ring
  rw [he]
  exact (defect_abs_six_add_le _ _ _ _ _ _).trans
    ((add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hqt hMix2)
      hHessBias) hDirBias) hScoreScaled) hMassScaled).trans_eq (by
        dsimp only [mixedStepDefectSecondBound]
        ring))

def stepQuadraticFirstSource (m : ℝ) (v : E) (f g : E → ℝ)
    (dm : ℝ) (w : E) (x : E) : ℝ :=
  g x+m*fderiv ℝ f x v*fderiv ℝ g x v+directionalJet v 2 g x/2+
    dm*(fderiv ℝ f x v)^2/2+directionSource m v w f x

theorem abs_firstVariationStep_sub_quadratic_le {B A a0 m : ℝ} {f g : E → ℝ}
    (hf : QPotential 4 B f) (hg : QBoundedJets 4 A g)
    (ha0 : 0 < a0) (hm : m ∈ Icc a0 1)
    (dm : ℝ) (v w x : E) (hv : ‖v‖ ≤ 1) :
    |firstVariationStep m v f g dm w x-stepQuadraticFirstSource m v f g dm w x| ≤
      (A*pathExpansionConstant B+|dm| *(2*B*pathExpansionConstant B/a0))*‖v‖^4+
        (B+4*B^2)*(1+B)^2*‖v‖^3*‖w‖ := by
  have hm0 : 0 < m := ha0.trans_le hm.1
  have hmcc : m ∈ Icc (0:ℝ) 1 := ⟨hm0.le,hm.2⟩
  have hG := abs_noiseMean_generator_remainder_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hg).potential (by norm_num) hmcc v x hv
  have hM := abs_mass_deriv_remainder_le hf le_rfl ha0 hm v x hv
  have hD : QBoundedJets 2 ((B+4*B^2)*‖v‖*‖w‖) (directionSource m v w f) := by
    simpa only [show (2:ℝ)^2 = 4 from by norm_num] using qBoundedJets_directionSource hf hmcc v w
  have hDb := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hD).potential (by norm_num) hmcc v x hv
  have hMb : |dm*(massSensitivity m v f x-(fderiv ℝ f x v)^2/2)| ≤
      |dm| *((2*B*pathExpansionConstant B/a0)*‖v‖^4) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hM (abs_nonneg _)
  have he : firstVariationStep m v f g dm w x-stepQuadraticFirstSource m v f g dm w x =
      (tiltedAverage m v f g x-g x-m*fderiv ℝ f x v*fderiv ℝ g x v-
        directionalJet v 2 g x/2)+dm*(massSensitivity m v f x-(fderiv ℝ f x v)^2/2)+
      (tiltedAverage m v f (directionSource m v w f) x-directionSource m v w f x) := by
    unfold firstVariationStep stepQuadraticFirstSource
    ring
  rw [he]
  exact (defect_abs_three_add_le _ _ _).trans
    ((add_le_add (add_le_add hG hMb) hDb).trans_eq (by ring))

def mixedStepUniformDefectCoefficient (B R a0 : ℝ) : ℝ :=
  R*pathExpansionConstant B+(R+B/a0)^2*potentialCovarianceDefectCoefficient B+
    (1+2/a0)*(2*B*pathExpansionConstant B/a0)+
    2*(1+4*B)*R*(1+B)^2+
    2*(R+B/a0)*mixedDirectionCovarianceDefectCoefficient B+
    B*secondNoiseBiasCoefficient B+noisyDirectionVarianceDefectCoefficient B+
    (B+4*B^2)*(1+B)^2

theorem mixedStepDefectSecondBound_le {B R A H a0 m dm ddm d : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hA : 0 ≤ A) (_hH : 0 ≤ H)
    (hAR : A ≤ R) (hHR : H ≤ R) (ha0 : 0 < a0) (hm : a0 ≤ m)
    (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1) (hd : 0 ≤ d)
    (v w b : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) :
    mixedStepDefectSecondBound B A H a0 m dm ddm v w b ≤
      mixedStepUniformDefectCoefficient B R a0*d^4 := by
  have hm0 : 0 < m := ha0.trans_le hm
  have hratio : |dm/m| ≤ 1/a0 := by
    rw [abs_div,abs_of_pos hm0]
    exact (div_le_div_of_nonneg_right hdm hm0.le).trans
      (one_div_le_one_div_of_le ha0 hm)
  have hdm2 : dm^2 ≤ 1 := by
    have H := pow_le_pow_left₀ (abs_nonneg dm) hdm 2
    simpa only [sq_abs,one_pow] using H
  have hmass : |ddm-2*dm^2/m| ≤ 1+2/a0 := by
    calc
      _ ≤ |ddm|+|2*dm^2/m| := abs_sub _ _
      _ = |ddm|+2*(dm^2/m) := by
        rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2),
          abs_of_nonneg (sq_nonneg dm),abs_of_pos hm0]
        ring
      _ ≤ 1+2*(1/a0) := by
        apply add_le_add hddm
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (div_le_div_of_nonneg_right hdm2 hm0.le).trans
          (one_div_le_one_div_of_le ha0 hm)
      _ = _ := by ring
  have hscore : A+|dm/m| *B ≤ R+B/a0 := by
    calc
      _ ≤ R+(1/a0)*B := add_le_add hAR (mul_le_mul_of_nonneg_right hratio hB)
      _ = _ := by ring
  have hP := pathExpansionConstant_nonneg hB
  have hQ := potentialCovarianceDefectCoefficient_nonneg hB
  have hJ : 0 ≤ secondNoiseBiasCoefficient B := by
    dsimp only [secondNoiseBiasCoefficient,defectNoiseMomentBound]; positivity
  have hM : 0 ≤ mixedDirectionCovarianceDefectCoefficient B := by
    dsimp only [mixedDirectionCovarianceDefectCoefficient]; positivity
  have hV : 0 ≤ noisyDirectionVarianceDefectCoefficient B := by
    dsimp only [noisyDirectionVarianceDefectCoefficient]; positivity
  unfold mixedStepDefectSecondBound
  calc
    _ ≤ (R*pathExpansionConstant B+(R+B/a0)^2*potentialCovarianceDefectCoefficient B+
        (1+2/a0)*(2*B*pathExpansionConstant B/a0))*d^4+
      (2*(1+4*B)*R*(1+B)^2+
        2*(R+B/a0)*mixedDirectionCovarianceDefectCoefficient B)*d^3*d+
      (B*secondNoiseBiasCoefficient B+noisyDirectionVarianceDefectCoefficient B)*d^2*d^2+
      (B+4*B^2)*(1+B)^2*d^3*d := by gcongr
    _ = _ := by dsimp only [mixedStepUniformDefectCoefficient]; ring

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem windowCurve_direction_three (β : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
        ‖(p k).2‖ ≤ D*Real.sqrt (h/(N:ℝ)) ∧
        ‖deriv (fun t => (p t).2) k‖ ≤ D*Real.sqrt (h/(N:ℝ)) ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ D*Real.sqrt (h/(N:ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (hbound β h hh N i k hk).2

theorem scalarData_window_mixedSecondSource_remainder {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ᶠ N : ℕ in atTop,
        ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap → ∀ x : E,
          let α := cdf (D.μ : Measure ℝ)
          let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
          let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
          let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
          let dm := deriv (fun t => (p t).1) k
          let ddm := deriv (deriv (fun t => (p t).1)) k
          let w := deriv (fun t => (p t).2) k
          let b := deriv (deriv (fun t => (p t).2)) k
          |secondVariationStep (p k).1 (p k).2 F (G 1) (G 2) dm ddm w b x-
            stepQuadraticSecondSource (p k).1 (p k).2 F (G 1) (G 2) dm ddm w b x| ≤
            K*h^2/(N:ℝ)^2 := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,hA,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    obtain ⟨L,hL,hdir⟩ := windowCurve_direction_three β
    let K := mixedStepUniformDefectCoefficient B R a0
    have hP := pathExpansionConstant_nonneg hB
    have hQ := potentialCovarianceDefectCoefficient_nonneg hB
    have hN2 : 0 ≤ secondNoiseBiasCoefficient B := by
      dsimp only [secondNoiseBiasCoefficient,defectNoiseMomentBound]; positivity
    have hM : 0 ≤ mixedDirectionCovarianceDefectCoefficient B := by
      dsimp only [mixedDirectionCovarianceDefectCoefficient]; positivity
    have hV2 : 0 ≤ noisyDirectionVarianceDefectCoefficient B := by
      dsimp only [noisyDirectionVarianceDefectCoefficient]; positivity
    have hK : 0 ≤ K := by dsimp only [K,mixedStepUniformDefectCoefficient]; positivity
    refine ⟨K*L^4,min hV (min hJ (min hE 1)),min kapE (1/2),by positivity,
      lt_min hhV (lt_min hhJ (lt_min hhE (by norm_num))),
      lt_min hkapE (by norm_num),?_⟩
    intro r hr h hh hh0
    have hhV' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhE' := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hlim : Tendsto (fun N : ℕ => L^2*h/(N:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (1:ℕ),
      hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with N hN hsmall
    intro lam hlam j k hk x
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
    let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
    have hkhalf := hk.trans (min_le_right _ _)
    have hp : p ∈ windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N :=
      orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hinputs := (hvar r hr h hh hhV' N hN lam hlam k hkhalf).2 p hp
    have hds := hdir _ _ _ hh.le N p hp k hkhalf
    let d := L*Real.sqrt (h/(N:ℝ))
    have hd : 0 ≤ d := by dsimp only [d]; positivity
    have hsq : d^2 = L^2*h/(N:ℝ) := by
      dsimp only [d]
      rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
      ring
    have hd1 : d ≤ 1 := by nlinarith [hsq,hsmall]
    obtain ⟨hG1,hG2⟩ := hjets r hr h hh hhJ' N hN lam hlam j k hkhalf
    have hRG : R*h ≤ R := mul_le_of_le_one_right hR.le hh1
    have hg : QBoundedJets 4 R (G 1) := (hG1.of_le (by norm_num : 4 ≤ 6)).mono hRG
    have hq : QBoundedJets 4 R (G 2) := hG2.mono hRG
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k (hk.trans (min_le_left _ _)) N hN
    obtain ⟨hinner,_⟩ := hEN lam hlam
    have hF : QPotential 4 B F := by
      simpa only [F,orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner j.val (by rw [windowMassPath_length]; exact j.isLt)).of_le (by norm_num : 4 ≤ 10)
    have H := abs_secondVariationStep_sub_quadratic_le hF hg hq ha0 hinputs.2.1
      (deriv (fun t => (p t).1) k) (deriv (deriv (fun t => (p t).1)) k)
      (p k).2 (deriv (fun t => (p t).2) k) (deriv (deriv (fun t => (p t).2)) k) x
      (hds.1.trans hd1)
    have H' := mixedStepDefectSecondBound_le hB hR.le hR.le hR.le le_rfl le_rfl ha0
      hinputs.2.1.1 hinputs.2.2.1 hinputs.2.2.2 hd _ _ _ hds.1 hds.2.1 hds.2.2
    have hd4 : d^4 = L^4*h^2/(N:ℝ)^2 := by
      calc
        d^4 = (d^2)^2 := by ring
        _ = (L^2*h/(N:ℝ))^2 := by rw [hsq]
        _ = _ := by ring
    exact (H.trans H').trans_eq (by rw [hd4]; dsimp only [K]; ring)
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner

namespace SKBarriers2.ParamChain

section DifferentiatedAverage

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance : NormedAddCommGroup (P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (P × X →L[ℝ] P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × X →L[ℝ] P × X →L[ℝ] ℝ) := inferInstance

theorem gaussianIntegral_curve_twoJet {W : P × (X × ℝ) → ℝ}
    (hW : ParamSmooth W) {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k)
    (x : X) :
    deriv (fun t => ∫ a, W (p t,(x,a)) ∂gaussianReal 0 1) k =
        ∫ a, deriv (fun t => W (p t,(x,a))) k ∂gaussianReal 0 1 ∧
      deriv (deriv (fun t => ∫ a, W (p t,(x,a)) ∂gaussianReal 0 1)) k =
        ∫ a, deriv (deriv (fun t => W (p t,(x,a)))) k ∂gaussianReal 0 1 := by
  let L : (P × X) × ℝ →L[ℝ] P × (X × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P X ℝ).toContinuousLinearMap
  let ι : P × (X × ℝ) → (P × X) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  let V : (P × X) × ℝ → ℝ := fun z => W (L z)
  let Z : P × X → ℝ := fun z => ∫ a, V (z,a) ∂gaussianReal 0 1
  let q := p k
  let u := deriv p k
  let b := deriv (deriv p) k
  have hV : ContDiff ℝ 2 V := hW.1.comp L.contDiff
  have hg : ParamExpGrowth (fun z : P × (X × ℝ) => V (ι z)) := hW.2.1
  have hg1 : ParamExpGrowth (fun z : P × (X × ℝ) => fderiv ℝ V (ι z)) :=
    param_reassoc_fderiv_growth (hW.1.differentiable (by norm_num)) hW.2.2.1
  have hg2 : ParamExpGrowth (fun z : P × (X × ℝ) => fderiv ℝ (fderiv ℝ V) (ι z)) :=
    param_second_compCLM_growth W L ι hW.1 hW.2.2.2
  have hZ : ContDiff ℝ 2 Z := param_contDiff_gaussian_integral V hV hg hg1 hg2
  have iD : Integrable (fun a => leftRestrict (fderiv ℝ V ((q,x),a)))
      (gaussianReal 0 1) :=
    (hg1.weakLocallyDominated.clm leftRestrict).integrable_section
      (leftRestrict.continuous.comp (hV.fderiv_right (m := 1) (by norm_num)).continuous) (q,x)
  have iDD : Integrable (fun a => secondLeftRestrict (fderiv ℝ (fderiv ℝ V) ((q,x),a)))
      (gaussianReal 0 1) :=
    (secondLeftRestrict_local_growth hg2.weakLocallyDominated).integrable_section
      (secondLeftRestrict.continuous.comp
        (hV.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous)
      (q,x)
  have hD (a : ℝ) (c : P) :
      leftRestrict (fderiv ℝ V ((q,x),a)) (c,0) =
        fderiv ℝ W (q,(x,a)) (c,0) := by
    have H := ((hW.1.differentiable (by norm_num) (L ((q,x),a))).hasFDerivAt.comp
      ((q,x),a) L.hasFDerivAt).fderiv
    change fderiv ℝ V ((q,x),a) = _ at H
    change fderiv ℝ V ((q,x),a) ((c,0),0) = _
    rw [H]
    rfl
  have hDD (a : ℝ) :
      secondLeftRestrict (fderiv ℝ (fderiv ℝ V) ((q,x),a)) (u,0) (u,0) =
        fderiv ℝ (fderiv ℝ W) (q,(x,a)) (u,0) (u,0) := by
    have H := second_affine_apply hW.1 L 0 ((q,x),a) ((u,0),0) ((u,0),0)
    simp only [add_zero] at H
    exact H
  have hfirst (a : ℝ) : deriv (fun t => W (p t,(x,a))) k =
      fderiv ℝ W (q,(x,a)) (u,0) :=
    ((hW.1.differentiable (by norm_num) (q,(x,a))).hasFDerivAt.comp_hasDerivAt k
      ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk
        (hasDerivAt_const k (x,a)))).deriv
  have hsecond (a : ℝ) : deriv (deriv (fun t => W (p t,(x,a)))) k =
      fderiv ℝ (fderiv ℝ W) (q,(x,a)) (u,0) (u,0)+
        fderiv ℝ W (q,(x,a)) (b,0) := second_parameter_curve hW.1 hp (x,a)
  constructor
  · have H := ((hZ.differentiable (by norm_num) (q,x)).hasFDerivAt.comp_hasDerivAt k
      ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k x))).deriv
    change deriv (fun t => ∫ a, W (p t,(x,a)) ∂gaussianReal 0 1) k = _ at H
    rw [H]
    change fderiv ℝ Z (q,x) (u,0) = _
    rw [show fderiv ℝ Z (q,x) = _ from
      fderiv_local_gaussian_integral V (hV.of_le (by norm_num))
        hg.weakLocallyDominated hg1.weakLocallyDominated (q,x),
      ContinuousLinearMap.integral_apply iD]
    simp_rw [hD,hfirst]
  · have H := second_parameter_curve hZ hp x
    change deriv (deriv (fun t => ∫ a, W (p t,(x,a)) ∂gaussianReal 0 1)) k = _ at H
    rw [H]
    change fderiv ℝ (fderiv ℝ Z) (q,x) (u,0) (u,0)+fderiv ℝ Z (q,x) (b,0) = _
    rw [show fderiv ℝ (fderiv ℝ Z) (q,x) = _ from
      fderiv_fderiv_local_gaussian_integral V hV hg.weakLocallyDominated
        hg1.weakLocallyDominated hg2.weakLocallyDominated (q,x),
      show fderiv ℝ Z (q,x) = _ from
      fderiv_local_gaussian_integral V (hV.of_le (by norm_num))
        hg.weakLocallyDominated hg1.weakLocallyDominated (q,x),
      ContinuousLinearMap.integral_apply iDD,
      ContinuousLinearMap.integral_apply (iDD.apply_continuousLinearMap (u,0)),
      ContinuousLinearMap.integral_apply iD,
      ← integral_add (iDD.apply_continuousLinearMap (u,0) |>.apply_continuousLinearMap (u,0))
        (iD.apply_continuousLinearMap (b,0))]
    simp_rw [hDD,hD,hsecond]

private theorem second_exp_mul_curve {a z : ℝ → ℝ} {k : ℝ}
    (ha : ContDiffAt ℝ 2 a k) (hz : ContDiffAt ℝ 2 z k) :
    deriv (deriv (fun t => Real.exp (a t)*z t)) k =
      Real.exp (a k)*(deriv (deriv z) k+2*deriv a k*deriv z k+
        (deriv (deriv a) k+deriv a k^2)*z k) := by
  have H := second_exp_neg_mul ha.neg hz
  have hfirst : deriv (fun t => -a t) = fun t => -deriv a t := funext (fun _ => deriv.neg)
  have hsecond : deriv (deriv (fun t => -a t)) k = -deriv (deriv a) k := by
    rw [hfirst]
    exact deriv.neg
  rw [hsecond,hfirst] at H
  simp only [neg_neg] at H
  exact H.trans (by ring)

private theorem second_quotient_curve {n z : ℝ → ℝ} {k : ℝ}
    (hn : ContDiffAt ℝ 2 n k) (hz : ContDiffAt ℝ 2 z k) (hzk : z k ≠ 0) :
    deriv (deriv (fun t => n t/z t)) k =
      deriv (deriv n) k/z k-2*(deriv n k/z k)*(deriv z k/z k)+
        (2*(deriv z k/z k)^2-deriv (deriv z) k/z k)*(n k/z k) := by
  let f := fun t => n t/z t
  have hf : ContDiffAt ℝ 2 f k := hn.div hz hzk
  have he : (fun t => z t*f t) =ᶠ[𝓝 k] n := by
    filter_upwards [hz.continuousAt.eventually_ne hzk] with t ht
    dsimp only [f]
    exact mul_div_cancel₀ (n t) ht
  have h1 := (((hz.differentiableAt (by norm_num)).hasDerivAt).fun_mul
    (hf.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [he.deriv_eq] at h1
  have h2 := iteratedDeriv_fun_mul hz hf
  rw [he.iteratedDeriv_eq 2] at h2
  norm_num only [Finset.sum_range_succ,Nat.choose_zero_right,Nat.choose_self,
    Nat.choose_one_right,iteratedDeriv_zero,iteratedDeriv_one,iteratedDeriv_succ,
    Finset.sum_range_zero,zero_add,one_mul,Nat.cast_ofNat,Nat.reduceSub] at h2
  change deriv (deriv n) k = z k * deriv (deriv f) k + 2*deriv z k*deriv f k+
    deriv (deriv z) k*f k at h2
  change deriv (deriv f) k = _
  have hf1 : deriv f k = (deriv n k-deriv z k*f k)/z k :=
    (eq_div_iff hzk).mpr (by nlinarith only [h1])
  calc
    _ = (deriv (deriv n) k-2*deriv z k*deriv f k-deriv (deriv z) k*f k)/z k :=
      (eq_div_iff hzk).mpr (by nlinarith only [h2])
    _ = _ := by rw [hf1]; dsimp only [f]; field_simp; ring

theorem gaussianAverage_curve_second {H G : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) :
    let U : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
    let J : (P × X) × ℝ → ℝ := fun z => G (z.1.1,(z.1.2,z.2))
    let μ := gaussianStepLaw 1 U (p k,x)
    let h1 := fun a => deriv (fun t => H (p t,(x,a))) k
    let h2 := fun a => deriv (deriv (fun t => H (p t,(x,a)))) k
    let g := fun a => G (p k,(x,a))
    let g1 := fun a => deriv (fun t => G (p t,(x,a))) k
    let g2 := fun a => deriv (deriv (fun t => G (p t,(x,a)))) k
    ContDiffAt ℝ 2 (fun t => OAI.SK.Analytic.gaussianAverage 1 U J (p t,x)) k ∧
      deriv (deriv (fun t => OAI.SK.Analytic.gaussianAverage 1 U J (p t,x))) k =
        (∫ a, g2 a+2*g1 a*h1 a+g a*(h2 a+h1 a^2) ∂μ)-
        2*(∫ a, g1 a+g a*h1 a ∂μ)*(∫ a, h1 a ∂μ)+
        (2*(∫ a, h1 a ∂μ)^2-(∫ a, h2 a+h1 a^2 ∂μ))*(∫ a, g a ∂μ) := by
  dsimp only
  let U : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
  let J : (P × X) × ℝ → ℝ := fun z => G (z.1.1,(z.1.2,z.2))
  let μ := gaussianStepLaw 1 U (p k,x)
  let Z := fun t => ∫ a, Real.exp (H (p t,(x,a))) ∂gaussianReal 0 1
  let N := fun t => ∫ a, Real.exp (H (p t,(x,a)))*G (p t,(x,a)) ∂gaussianReal 0 1
  have hZ : ContDiffAt ℝ 2 Z k :=
    (hH.expSmooth.gaussian_integral.1.contDiffAt).comp k (hp.prodMk contDiffAt_const)
  have hN : ContDiffAt ℝ 2 N k :=
    ((hH.expSmooth.mul hG).gaussian_integral.1.contDiffAt).comp k (hp.prodMk contDiffAt_const)
  have hz : Z k ≠ 0 := by simpa only [Z,one_mul] using (hH.exp_gaussian_pos 1 (p k,x)).ne'
  have he : (fun t => OAI.SK.Analytic.gaussianAverage 1 U J (p t,x)) = fun t => N t/Z t := by
    funext t
    simpa only [OAI.SK.Analytic.gaussianAverage,Z,N,U,J,one_mul,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      gaussianStepLaw_integral_inv_smul 1 U (p t,x) (fun a => G (p t,(x,a)))
  refine ⟨((ParamSmooth.gaussianAverage hH hG 1).1.contDiffAt).comp k (hp.prodMk contDiffAt_const),?_⟩
  rw [he,second_quotient_curve hN hZ hz]
  have hpH (a : ℝ) : ContDiffAt ℝ 2 (fun t => H (p t,(x,a))) k :=
    hH.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)
  have hpG (a : ℝ) : ContDiffAt ℝ 2 (fun t => G (p t,(x,a))) k :=
    hG.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)
  have hZjets := gaussianIntegral_curve_twoJet hH.expSmooth hp x
  have hNjets := gaussianIntegral_curve_twoJet (hH.expSmooth.mul hG) hp x
  have normMoment (a : ℝ → ℝ) :
      (∫ t, Real.exp (H (p k,(x,t)))*a t ∂gaussianReal 0 1)/Z k = ∫ t, a t ∂μ := by
    simpa only [μ,Z,U,one_mul,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      (gaussianStepLaw_integral_inv_smul 1 U (p k,x) a).symm
  have hZ1 : deriv Z k/Z k =
      ∫ a, deriv (fun t => H (p t,(x,a))) k ∂μ := by
    rw [hZjets.1]
    simp_rw [((hpH _).differentiableAt (by norm_num)).hasDerivAt.exp.deriv]
    exact normMoment _
  have hN1 : deriv N k/Z k =
      ∫ a, deriv (fun t => G (p t,(x,a))) k+
        G (p k,(x,a))*deriv (fun t => H (p t,(x,a))) k ∂μ := by
    rw [hNjets.1]
    have hpoint (a : ℝ) :
        deriv (fun t => Real.exp (H (p t,(x,a)))*G (p t,(x,a))) k =
          Real.exp (H (p k,(x,a)))*(deriv (fun t => G (p t,(x,a))) k+
            G (p k,(x,a))*deriv (fun t => H (p t,(x,a))) k) := by
      rw [(((hpH a).differentiableAt (by norm_num)).hasDerivAt.exp.fun_mul
        ((hpG a).differentiableAt (by norm_num)).hasDerivAt).deriv]
      ring
    simp_rw [hpoint]
    exact normMoment _
  have hZ2 : deriv (deriv Z) k/Z k =
      ∫ a, deriv (deriv (fun t => H (p t,(x,a)))) k+
        (deriv (fun t => H (p t,(x,a))) k)^2 ∂μ := by
    rw [hZjets.2]
    have hpoint (a : ℝ) : deriv (deriv (fun t => Real.exp (H (p t,(x,a))))) k =
        Real.exp (H (p k,(x,a)))*(deriv (deriv (fun t => H (p t,(x,a)))) k+
          (deriv (fun t => H (p t,(x,a))) k)^2) := by
      simpa only [mul_one,deriv_const',deriv_const,zero_mul,mul_zero,add_zero,zero_add] using
        second_exp_mul_curve (hpH a) (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => (1:ℝ)) k)
    simp_rw [hpoint]
    exact normMoment _
  have hN2 : deriv (deriv N) k/Z k =
      ∫ a, deriv (deriv (fun t => G (p t,(x,a)))) k+
        2*deriv (fun t => G (p t,(x,a))) k*deriv (fun t => H (p t,(x,a))) k+
        G (p k,(x,a))*(deriv (deriv (fun t => H (p t,(x,a)))) k+
          (deriv (fun t => H (p t,(x,a))) k)^2) ∂μ := by
    rw [hNjets.2]
    have hpoint (a : ℝ) : deriv (deriv (fun t => Real.exp (H (p t,(x,a)))*G (p t,(x,a)))) k =
        Real.exp (H (p k,(x,a)))*(deriv (deriv (fun t => G (p t,(x,a)))) k+
          2*deriv (fun t => G (p t,(x,a))) k*deriv (fun t => H (p t,(x,a))) k+
          G (p k,(x,a))*(deriv (deriv (fun t => H (p t,(x,a)))) k+
            (deriv (fun t => H (p t,(x,a))) k)^2)) := by
      exact (second_exp_mul_curve (hpH a) (hpG a)).trans (by congr 1; ring)
    simp_rw [hpoint]
    exact normMoment _
  rw [hZ1,hZ2,hN1,hN2,show N k/Z k = ∫ a, G (p k,(x,a)) ∂μ from normMoment _]

theorem gaussianAverage_curve_first {H G : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) :
    let U : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
    let J : (P × X) × ℝ → ℝ := fun z => G (z.1.1,(z.1.2,z.2))
    let μ := gaussianStepLaw 1 U (p k,x)
    deriv (fun t => OAI.SK.Analytic.gaussianAverage 1 U J (p t,x)) k =
      (∫ a, deriv (fun t => G (p t,(x,a))) k+
        G (p k,(x,a))*deriv (fun t => H (p t,(x,a))) k ∂μ)-
      (∫ a, G (p k,(x,a)) ∂μ)*(∫ a, deriv (fun t => H (p t,(x,a))) k ∂μ) := by
  dsimp only
  let U : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
  let J : (P × X) × ℝ → ℝ := fun z => G (z.1.1,(z.1.2,z.2))
  let μ := gaussianStepLaw 1 U (p k,x)
  let Z := fun t => ∫ a, Real.exp (H (p t,(x,a))) ∂gaussianReal 0 1
  let N := fun t => ∫ a, Real.exp (H (p t,(x,a)))*G (p t,(x,a)) ∂gaussianReal 0 1
  have hZ : ContDiffAt ℝ 2 Z k :=
    (hH.expSmooth.gaussian_integral.1.contDiffAt).comp k (hp.prodMk contDiffAt_const)
  have hN : ContDiffAt ℝ 2 N k :=
    ((hH.expSmooth.mul hG).gaussian_integral.1.contDiffAt).comp k (hp.prodMk contDiffAt_const)
  have hz : Z k ≠ 0 := by simpa only [Z,one_mul] using (hH.exp_gaussian_pos 1 (p k,x)).ne'
  have he : (fun t => OAI.SK.Analytic.gaussianAverage 1 U J (p t,x)) = fun t => N t/Z t := by
    funext t
    simpa only [OAI.SK.Analytic.gaussianAverage,Z,N,U,J,one_mul,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      gaussianStepLaw_integral_inv_smul 1 U (p t,x) (fun a => G (p t,(x,a)))
  have hpH (a : ℝ) : ContDiffAt ℝ 2 (fun t => H (p t,(x,a))) k :=
    hH.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)
  have hpG (a : ℝ) : ContDiffAt ℝ 2 (fun t => G (p t,(x,a))) k :=
    hG.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)
  have normMoment (a : ℝ → ℝ) :
      (∫ t, Real.exp (H (p k,(x,t)))*a t ∂gaussianReal 0 1)/Z k = ∫ t, a t ∂μ := by
    simpa only [μ,Z,U,one_mul,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      (gaussianStepLaw_integral_inv_smul 1 U (p k,x) a).symm
  have hZ1 : deriv Z k/Z k = ∫ a, deriv (fun t => H (p t,(x,a))) k ∂μ := by
    rw [(gaussianIntegral_curve_twoJet hH.expSmooth hp x).1]
    simp_rw [((hpH _).differentiableAt (by norm_num)).hasDerivAt.exp.deriv]
    exact normMoment _
  have hN1 : deriv N k/Z k = ∫ a, deriv (fun t => G (p t,(x,a))) k+
      G (p k,(x,a))*deriv (fun t => H (p t,(x,a))) k ∂μ := by
    rw [(gaussianIntegral_curve_twoJet (hH.expSmooth.mul hG) hp x).1]
    have hpoint (a : ℝ) :
        deriv (fun t => Real.exp (H (p t,(x,a)))*G (p t,(x,a))) k =
          Real.exp (H (p k,(x,a)))*(deriv (fun t => G (p t,(x,a))) k+
            G (p k,(x,a))*deriv (fun t => H (p t,(x,a))) k) := by
      rw [(((hpH a).differentiableAt (by norm_num)).hasDerivAt.exp.fun_mul
        ((hpG a).differentiableAt (by norm_num)).hasDerivAt).deriv]
      ring
    simp_rw [hpoint]
    exact normMoment _
  rw [he,(((hN.differentiableAt (by norm_num)).hasDerivAt).fun_div
    (hZ.differentiableAt (by norm_num)).hasDerivAt hz).deriv]
  calc
    _ = deriv N k/Z k-(N k/Z k)*(deriv Z k/Z k) := by field_simp
    _ = _ := by rw [hZ1,hN1,show N k/Z k = ∫ a, G (p k,(x,a)) ∂μ from normMoment _]

end DifferentiatedAverage

end SKBarriers2.ParamChain

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def firstTiltedAverageSource (m : ℝ) (v : E) (f F g a : E → ℝ)
    (dm : ℝ) (w : E) (x : E) : ℝ :=
  tiltedAverage m v f a x+
    tiltedAverage m v f (mixedDirectionSource m v w f g) x+
    dm*covariance (fun t => g (x+t • v)) (fun t => f (x+t • v)) (stepLaw m v f x)+
    m*spatialCovariance m v f g F x+
    m*spatialCovariance m v f g (directionSource m v w f) x+
    m*tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x

def firstTiltedAverageSourceBound (B A C D m dm : ℝ) (v w : E) : ℝ :=
  D+tiltedStabilityCoefficient 2 B*D*‖v‖^2+
    tiltedCoarseCoefficient 2 B*(1+4*B)*C*‖v‖*‖w‖+
    |dm| *(potentialCovarianceCoefficient 2 B*C*B*‖v‖^2)+
    |m| *(covarianceJetCoefficient 2 B*C*A*‖v‖^2)+
    |m| *(covarianceJetCoefficient 2 B*C*(B+8*B^2)*‖v‖*‖w‖*‖v‖^2)+
    |m| *(tiltedCoarseCoefficient 2 B*4*C*B*‖v‖*‖w‖)

theorem qBoundedJets_firstTiltedAverageSource {B A C D : ℝ} {f F g a : E → ℝ}
    (hf : QPotential 5 B f) (hF : QBoundedJets 3 A F)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 2 D a)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (dm : ℝ) (v w : E)
    (hv : ‖v‖ ≤ 1) (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets 2 (firstTiltedAverageSourceBound B A C D m dm v w)
      (firstTiltedAverageSource m v f F g a dm w) := by
  have hT := qBoundedJets_tiltedAverage 2 hf (by norm_num) (by norm_num) ha hm v hsmall
  have hM := qBoundedJets_tiltedAverage_coarse 2 hf (by norm_num) (by norm_num)
    (qBoundedJets_mixedDirectionSource_order (hf.of_le (by norm_num : 4 ≤ 5)) hg hm v w)
    hm v
  have hgp : QPotential 4 C g := (qBoundedJets_iff_qBddSmooth.mp hg).potential
  have hC := (qBoundedJets_potentialCovariance (n := 2)
    (hf.of_le (by norm_num : 4 ≤ 5)) hgp (hf.of_le (by norm_num : 4 ≤ 5)) hm v hv).const_smul dm
  have hF' := (qBoundedJets_spatialCovariance 2 hf (by norm_num) (by norm_num)
    (hg.of_le (by norm_num : 3 ≤ 4)) hF hm v hsmall).const_smul m
  have hdir := qBoundedJets_directionSource hf hm v w
  have hD := (qBoundedJets_spatialCovariance 2 hf (by norm_num) (by norm_num)
    (hg.of_le (by norm_num : 3 ≤ 4)) hdir hm v hsmall).const_smul m
  have hprod := ((hg.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const v).mul
    ((hf.derivativeJets.of_le (by norm_num : 2 ≤ 4)).apply_const w)
  have hP := (qBoundedJets_tiltedAverage_coarse 2 hf (by norm_num) (by norm_num)
    hprod hm v).const_smul m
  convert ((((hT.add hM).add hC).add hF').add hD).add hP using 1
  · dsimp only [firstTiltedAverageSourceBound]
    norm_num
    ring
  · rfl

theorem firstTiltedAverageSource_eq_score {B A C : ℝ} {f F g : E → ℝ}
    (hf : QPotential 4 B f) (hF : QBoundedJets 3 A F) (hg : QBoundedJets 3 C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (η : ℝ) (v w x : E) (a : E → ℝ) :
    firstTiltedAverageSource m v f F g a (m*η) w x =
      tiltedAverage m v f a x+
        noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) w)+
        m*covariance (fun t => g (x+t • v))
          (fun t => F (x+t • v)+η*f (x+t • v)+t*fderiv ℝ f (x+t • v) w)
          (stepLaw m v f x) := by
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hgp : QPotential 3 C g := (qBoundedJets_iff_qBddSmooth.mp hg).potential
  have hFp : QPotential 3 A F := (qBoundedJets_iff_qBddSmooth.mp hF).potential
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  let Y := fun t => t*fderiv ℝ f (x+t • v) w
  have hgm := defect_potential_memLp hf3 hgp m v x
  have hFm := defect_potential_memLp hf3 hFp m v x
  have hfm := defect_potential_memLp hf3 hf3 m v x
  have hW := (hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w
  have hYm : MemLp Y 2 μ := memLp_noise_of_growth hf3 m v x
    (continuous_id.mul (hW.smooth.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))))
    ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).mul
      (HasExpGrowth.of_bounded hW.nonneg (fun t => hW.norm_le _)))
  have hsplit : covariance (fun t => g (x+t • v))
      (fun t => F (x+t • v)+η*f (x+t • v)+Y t) μ =
      covariance (fun t => g (x+t • v)) (fun t => F (x+t • v)) μ+
        η*covariance (fun t => g (x+t • v)) (fun t => f (x+t • v)) μ+
        covariance (fun t => g (x+t • v)) Y μ := by
    change covariance (fun t => g (x+t • v))
      (((fun t => F (x+t • v))+(fun t => η*f (x+t • v)))+Y) (stepLaw m v f x) = _
    rw [covariance_add_right hgm (hFm.add (hfm.const_mul η)) hYm,
      covariance_add_right hgm hFm (hfm.const_mul η),covariance_const_mul_right]
  have hcovF := spatialCovariance_eq hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 1 ≤ 3)))
    (qBoundedJets_iff_qBddSmooth.mp (hF.of_le (by norm_num : 1 ≤ 3))) m v x
  rw [hsplit,← hcovF,covariance_noisy_direction_eq hf hgp hm v w x,
    noise_mixedDirectionSource hf3 hg m v w x]
  unfold firstTiltedAverageSource
  ring

section ActualFirstAverage

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem deriv_exponential_movingAverage {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B A C D : ℝ}
    (hf : QPotential 4 B (fun y => F (p k,y)))
    (hF1 : QBoundedJets 3 A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hg : QBoundedJets 3 C (fun y => G (p k,y)))
    (ha : QBoundedJets 1 D (fun y => fderiv ℝ G (p k,y) (deriv p k,0)))
    (hm : Real.exp (M (p k)) ≤ 1) (x : E) :
    deriv (fun t => tiltedAverage (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) (fun y => G (p t,y)) x) k =
      firstTiltedAverageSource (Real.exp (M (p k))) (V (p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => G (p k,y)) (fun y => fderiv ℝ G (p k,y) (deriv p k,0))
        (Real.exp (M (p k))*M (deriv p k)) (V (deriv p k)) x := by
  let q := p k
  let u := deriv p k
  let m := Real.exp (M q)
  let v := V q
  let w := V u
  let f := fun y => F (q,y)
  let F1 := fun y => fderiv ℝ F (q,y) (u,0)
  let g := fun y => G (q,y)
  let a := fun y => fderiv ℝ G (q,y) (u,0)
  let H := ParamChain.movingLogInput F M V
  let J := fun z : P × (E × ℝ) => G (z.1,z.2.1+z.2.2 • V z.1)
  let μ := stepLaw m v f x
  have hH : ParamRegular H := ParamChain.regular_movingLogInput hF M V
  have hJ : ParamSmooth J := ParamChain.smooth_movingInput hG V
  have hnorm := ParamChain.gaussianAverage_curve_first hH hJ hp x
  dsimp only at hnorm
  have hlaw : gaussianStepLaw 1 (fun z : (P × E) × ℝ => H (z.1.1,(z.1.2,z.2))) (q,x) = μ := by
    simp only [μ,stepLaw,gaussianStepLaw,H,ParamChain.movingLogInput,one_mul]
    rfl
  have hinput (t : ℝ) : deriv (fun b => H (p b,(x,t))) k =
      m*(F1 (x+t • v)+M u*f (x+t • v)+t*fderiv ℝ f (x+t • v) w) := by
    have hd := ((hH.1.differentiable (by norm_num) (q,(x,t))).hasFDerivAt.comp_hasDerivAt k
      ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k (x,t)))).deriv
    change deriv (fun b => H (p b,(x,t))) k = fderiv ℝ H (q,(x,t)) (u,0) at hd
    rw [hd]
    exact ParamChain.movingLogInput_first_source hF M V q u x t
  have htest (t : ℝ) : deriv (fun b => J (p b,(x,t))) k =
      a (x+t • v)+t*fderiv ℝ g (x+t • v) w := by
    have hv0 : HasDerivAt (fun b => V (p b)) w k :=
      V.hasFDerivAt.comp_hasDerivAt k (hp.differentiableAt (by norm_num)).hasDerivAt
    have hv : HasDerivAt (fun b => x+t • V (p b)) (t • w) k := by
      convert! ((hasDerivAt_const k t).smul hv0).const_add x using 1
      simp only [zero_smul,add_zero]
    have hd := ((hG.1.differentiable (by norm_num) (q,x+t • v)).hasFDerivAt.comp_hasDerivAt k
      ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk hv)).deriv
    change deriv (fun b => J (p b,(x,t))) k = fderiv ℝ G (q,x+t • v) (u,t • w) at hd
    rw [hd]
    have hsp := ((hG.1.differentiable (by norm_num) (q,x+t • v)).hasFDerivAt.comp
      (x+t • v) ((hasFDerivAt_const q (x+t • v)).prodMk (hasFDerivAt_id (x+t • v)))).fderiv
    have he : (u,t • w) = (u,(0:E))+t • ((0:P),w) := by ext <;> simp
    rw [he,map_add,map_smul]
    change a (x+t • v)+t*fderiv ℝ G (q,x+t • v) (0,w) = _
    have hs : fderiv ℝ g (x+t • v) w = fderiv ℝ G (q,x+t • v) (0,w) :=
      congrArg (fun L : E →L[ℝ] ℝ => L w) hsp
    rw [hs]
  have heq : (fun b => OAI.SK.Analytic.gaussianAverage 1
      (fun z : (P × E) × ℝ => H (z.1.1,(z.1.2,z.2)))
      (fun z : (P × E) × ℝ => J (z.1.1,(z.1.2,z.2))) (p b,x)) =
      fun b => tiltedAverage (Real.exp (M (p b))) (V (p b))
        (fun y => F (p b,y)) (fun y => G (p b,y)) x := by
    funext b
    simp only [OAI.SK.Analytic.gaussianAverage,tiltedAverage,stepLaw,gaussianStepLaw,H,J,
      ParamChain.movingLogInput,one_mul]
    rfl
  rw [heq,hlaw] at hnorm
  simp_rw [hinput,htest] at hnorm
  let S := fun t => F1 (x+t • v)+M u*f (x+t • v)+t*fderiv ℝ f (x+t • v) w
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hgm : MemLp (fun t => g (x+t • v)) 2 μ :=
    defect_potential_memLp hf3 (qBoundedJets_iff_qBddSmooth.mp hg).potential m v x
  have hS : MemLp S 2 μ := memLp_secondScore hf3 hF1 m (M u) v w x
  have hiA : Integrable (fun t => a (x+t • v)) μ :=
    integrable_tilted_shift hf (by norm_num) ha m v x
  have hiD : Integrable (fun t => t*fderiv ℝ g (x+t • v) w) μ :=
    (integrable_noise_test_powers hf3
      ((hg.derivativeJets.apply_const w).of_le (by norm_num : 1 ≤ 2)) m v x).1
  have hiP := defect_integrable_mul hgm hS
  have hsplit :
      (∫ t, a (x+t • v)+t*fderiv ℝ g (x+t • v) w+
        g (x+t • v)*(m*S t) ∂μ)-
        (∫ t, g (x+t • v) ∂μ)*(∫ t, m*S t ∂μ) =
      tiltedAverage m v f a x+noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) w)+
        m*covariance (fun t => g (x+t • v)) S μ := by
    have hp : (fun t => g (x+t • v)*(m*S t)) = fun t => m*(g (x+t • v)*S t) :=
      funext (fun _ => by ring)
    have hiAD : Integrable (fun t => a (x+t • v)+t*fderiv ℝ g (x+t • v) w) μ :=
      (hiA.add hiD).congr (ae_of_all μ (fun _ => by simp only [Pi.add_apply]))
    have hiMP : Integrable (fun t => g (x+t • v)*(m*S t)) μ := by
      rw [hp]
      exact hiP.const_mul m
    rw [integral_add (f := fun t => a (x+t • v)+t*fderiv ℝ g (x+t • v) w)
        (g := fun t => g (x+t • v)*(m*S t)) hiAD hiMP,
      integral_add hiA hiD,hp,integral_const_mul,integral_const_mul,covariance_eq_sub hgm hS]
    dsimp only [tiltedAverage,noiseMean,μ]
    simp only [Pi.mul_apply]
    ring
  change deriv (fun b => tiltedAverage (Real.exp (M (p b))) (V (p b))
    (fun y => F (p b,y)) (fun y => G (p b,y)) x) k = _ at hnorm
  change _ = firstTiltedAverageSource m v f F1 g a (m*M u) w x
  rw [firstTiltedAverageSource_eq_score hf hF1 hg ⟨(Real.exp_pos _).le,hm⟩ (M u) v w x a]
  exact hnorm.trans hsplit

theorem qBoundedJets_deriv_exponential_movingAverage {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B A C D : ℝ}
    (hf : QPotential 5 B (fun y => F (p k,y)))
    (hF1 : QBoundedJets 3 A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hg : QBoundedJets 4 C (fun y => G (p k,y)))
    (ha : QBoundedJets 2 D (fun y => fderiv ℝ G (p k,y) (deriv p k,0)))
    (hm : Real.exp (M (p k)) ≤ 1) (hv : ‖V (p k)‖ ≤ 1)
    (hsmall : Real.exp (M (p k))*(B*‖V (p k)‖^2) ≤ 1/2) :
    QBoundedJets 2 (firstTiltedAverageSourceBound B A C D (Real.exp (M (p k)))
      (Real.exp (M (p k))*M (deriv p k)) (V (p k)) (V (deriv p k)))
      (fun x => deriv (fun t => tiltedAverage (Real.exp (M (p t))) (V (p t))
        (fun y => F (p t,y)) (fun y => G (p t,y)) x) k) := by
  have he : (fun x => deriv (fun t => tiltedAverage (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) (fun y => G (p t,y)) x) k) =
      firstTiltedAverageSource (Real.exp (M (p k))) (V (p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => G (p k,y)) (fun y => fderiv ℝ G (p k,y) (deriv p k,0))
        (Real.exp (M (p k))*M (deriv p k)) (V (deriv p k)) :=
    funext (deriv_exponential_movingAverage hF hG M V hp (hf.of_le (by norm_num)) hF1
      (hg.of_le (by norm_num)) (ha.of_le (by norm_num)) hm)
  rw [he]
  exact qBoundedJets_firstTiltedAverageSource hf hF1 hg ha ⟨(Real.exp_pos _).le,hm⟩ _ _ _ hv hsmall

end ActualFirstAverage

def firstTiltedTransportCoefficient (B R : ℝ) : ℝ :=
  |tiltedCoarseCoefficient 2 B*(1+4*B)|+
    |potentialCovarianceCoefficient 2 B*B|+|covarianceJetCoefficient 2 B| *R+
    |covarianceJetCoefficient 2 B*(B+8*B^2)|+|tiltedCoarseCoefficient 2 B*4*B|

theorem firstTiltedAverageSourceBound_le {B A C D R m dm : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R) (hAR : A ≤ R)
    (hm : m ∈ Icc (0:ℝ) 1) (hdm : |dm| ≤ 1) (v w : E) (hv : ‖v‖ ≤ 1) :
    firstTiltedAverageSourceBound B A C D m dm v w ≤
      (1+|tiltedStabilityCoefficient 2 B| *‖v‖^2)*D+
        firstTiltedTransportCoefficient B R*C*(‖v‖^2+‖w‖^2) := by
  let e := ‖v‖^2+‖w‖^2
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hvs : ‖v‖^2 ≤ e := by dsimp only [e]; nlinarith [sq_nonneg ‖w‖]
  have hvw : ‖v‖*‖w‖ ≤ e := by
    dsimp only [e]
    nlinarith [sq_nonneg (‖v‖-‖w‖),sq_nonneg ‖v‖,sq_nonneg ‖w‖]
  have hv2 : ‖v‖^2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hvsw : ‖v‖*‖w‖*‖v‖^2 ≤ e :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg v) (norm_nonneg w)) hv2).trans hvw
  have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
  have hcoef {a t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t*a ≤ |a| :=
    (mul_le_mul_of_nonneg_left (le_abs_self a) ht0).trans
      (mul_le_of_le_one_left (abs_nonneg a) ht1)
  have hmass := hcoef (a := potentialCovarianceCoefficient 2 B*B) (abs_nonneg dm) hdm
  have hvar : |m| *covarianceJetCoefficient 2 B*A ≤ |covarianceJetCoefficient 2 B| *R := by
    exact (mul_le_mul_of_nonneg_right
      (hcoef (a := covarianceJetCoefficient 2 B) (abs_nonneg m) hmabs) hA).trans
      (mul_le_mul_of_nonneg_left hAR (abs_nonneg _))
  have hdir := hcoef (a := covarianceJetCoefficient 2 B*(B+8*B^2)) (abs_nonneg m) hmabs
  have hprod := hcoef (a := tiltedCoarseCoefficient 2 B*4*B) (abs_nonneg m) hmabs
  have hterm {a K t : ℝ} (ha : a ≤ K) (hK : 0 ≤ K) (ht : 0 ≤ t) (hte : t ≤ e) :
      a*C*t ≤ K*C*e :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hC) ht).trans
      (mul_le_mul_of_nonneg_left hte (mul_nonneg hK hC))
  have h1 := hterm (le_abs_self (tiltedCoarseCoefficient 2 B*(1+4*B))) (abs_nonneg _)
    (mul_nonneg (norm_nonneg v) (norm_nonneg w)) hvw
  have h2 := hterm hmass (abs_nonneg _) (sq_nonneg ‖v‖) hvs
  have h3 := hterm hvar (mul_nonneg (abs_nonneg _) hR) (sq_nonneg ‖v‖) hvs
  have h4 := hterm hdir (abs_nonneg _) (by positivity) hvsw
  have h5 := hterm hprod (abs_nonneg _) (mul_nonneg (norm_nonneg v) (norm_nonneg w)) hvw
  have h0 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self (tiltedStabilityCoefficient 2 B)) hD)
    (sq_nonneg ‖v‖)
  dsimp only [firstTiltedAverageSourceBound,firstTiltedTransportCoefficient]
  dsimp only [e] at h1 h2 h3 h4 h5
  nlinarith only [h0,h1,h2,h3,h4,h5]

theorem abs_second_deriv_exponentialStep_sub_quadratic_le
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B A H a0 : ℝ}
    (hf : QPotential 4 B (fun y => F (p k,y)))
    (hg : QBoundedJets 4 A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hq : QBoundedJets 4 H (fun y =>
      fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0)+
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0)))
    (ha0 : 0 < a0) (hm : Real.exp (M (p k)) ∈ Icc a0 1) (x : E)
    (hv : ‖V (p k)‖ ≤ 1) :
    let f := fun y => F (p k,y)
    let g := fun y => fderiv ℝ F (p k,y) (deriv p k,0)
    let q := fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0)+
      fderiv ℝ F (p k,y) (deriv (deriv p) k,0)
    let m := Real.exp (M (p k))
    let v := V (p k)
    let dm := m*M (deriv p k)
    let ddm := m*((M (deriv p k))^2+M (deriv (deriv p) k))
    let w := V (deriv p k)
    let b := V (deriv (deriv p) k)
    |deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
        (fun y => F (p t,y)) x)) k-stepQuadraticSecondSource m v f g q dm ddm w b x| ≤
      mixedStepDefectSecondBound B A H a0 m dm ddm v w b := by
  dsimp only
  rw [second_deriv_exponential_movingStep hF M V hp (hf.of_le (by norm_num : 3 ≤ 4))
    (hg.of_le (by norm_num : 3 ≤ 4)) (hq.of_le (by norm_num : 1 ≤ 4)) x]
  exact abs_secondVariationStep_sub_quadratic_le hf hg hq ha0 hm _ _ _ _ _ x hv

end SKBarriers2.StepCalculus
