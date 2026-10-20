module

public import SKBarriers2.Corner.PathEnergyGenerator4

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def secondMovingAverageQuadratic (m dm ddm : ℝ) (v w b : E)
    (f f₁ f₂ g a q : E → ℝ) (x : E) : ℝ :=
  q x+pathGenerator m v f q x+2*mixedDirectionSource m v w f a x+
    mixedDirectionSource m v b f g x+fderiv ℝ (fderiv ℝ g) x w w+
    2*(fderiv ℝ a x v+fderiv ℝ g x w)*
      (dm*fderiv ℝ f x v+m*(fderiv ℝ f₁ x v+fderiv ℝ f x w))+
    fderiv ℝ g x v*(ddm*fderiv ℝ f x v+
      2*dm*(fderiv ℝ f₁ x v+fderiv ℝ f x w)+
      m*(fderiv ℝ f₂ x v+2*fderiv ℝ f₁ x w+fderiv ℝ f x b))

theorem memLp_step_noise_of_polynomial_bound {B K : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (m : ℝ) (v x : E) {G : ℝ → ℝ} (p : ℕ)
    (hc : Continuous G) (hK : 0 ≤ K) (hbound : ∀ t, |G t| ≤ K*|t|^p) :
    MemLp G 2 (stepLaw m v f x) := by
  apply memLp_noise_of_growth hf m v x hc
  have hpow : HasExpGrowth (fun t : ℝ => t^p) := by
    simpa only [ContinuousLinearMap.id_apply] using
      (HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).pow p
  apply hpow.congr_bound hK
  intro t
  simpa only [Real.norm_eq_abs,abs_pow] using hbound t

theorem integrable_step_noise_abs_power {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (m : ℝ) (v x : E) (p : ℕ) :
    Integrable (fun t : ℝ => |t|^p) (stepLaw m v f x) := by
  have hpow : HasExpGrowth (fun t : ℝ => t^p) := by
    simpa only [ContinuousLinearMap.id_apply] using
      (HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).pow p
  have hnorm := hpow.norm (fun t => norm_nonneg (t^p))
  have habs : HasExpGrowth (fun t : ℝ => |t|^p) := by
    simpa only [Real.norm_eq_abs,abs_pow] using hnorm
  exact integrable_noise hf (by norm_num) m v x habs (continuous_abs.pow p)

theorem abs_step_noise_variance_sub_one_le {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) :
    |covariance (fun t : ℝ => t) (fun t : ℝ => t) (stepLaw m v f x)-1| ≤
      (B+2*B^2)*‖v‖^2 := by
  have hB := hf.nonneg
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hi : MemLp (fun t : ℝ => t) 2 μ :=
    memLp_step_noise_of_polynomial_bound (K := 1) hf m v x 1 continuous_id (by norm_num)
      (by intro t; simp only [pow_one,one_mul,le_refl])
  have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
  have hfirst : |noiseMean m v f x (fun t => t)| ≤ B*‖v‖ :=
    (abs_noise_first_le hf (by norm_num) m v x).trans
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hB hmabs) (norm_nonneg v))
  have hsecond : |noiseMean m v f x (fun t => t^2)-1| ≤ (B+B^2)*‖v‖^2 := by
    apply (abs_noise_second_sub_one_le hf (by norm_num) m v x).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [abs_of_nonneg hm.1]
    have hm2 : m^2 ≤ 1 := by nlinarith only [hm.1,hm.2]
    nlinarith only [mul_le_mul_of_nonneg_right hm.2 hB,
      mul_le_mul_of_nonneg_right hm2 (sq_nonneg B)]
  have hc : covariance (fun t : ℝ => t) (fun t : ℝ => t) μ =
      noiseMean m v f x (fun t => t^2)-noiseMean m v f x (fun t => t)^2 := by
    rw [covariance_eq_sub hi hi]
    simp only [Pi.mul_apply,pow_two]
    rfl
  rw [hc]
  have he : noiseMean m v f x (fun t => t^2)-noiseMean m v f x (fun t => t)^2-1 =
      (noiseMean m v f x (fun t => t^2)-1)-noiseMean m v f x (fun t => t)^2 := by ring
  rw [he]
  calc
    _ ≤ |noiseMean m v f x (fun t => t^2)-1|+
        |noiseMean m v f x (fun t => t)^2| := abs_sub _ _
    _ ≤ (B+B^2)*‖v‖^2+(B*‖v‖)^2 := by
      apply add_le_add hsecond
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hfirst 2
    _ = _ := by ring

theorem abs_noise_movingTestSecond_sub_quadratic_le {B C d : ℝ}
    {f g a q : E → ℝ} (hf : QPotential 4 B f)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 C a) (hq : QBoundedJets 4 C q)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (v w b x : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) :
    |noiseMean m v f x (movingAverageTestSecond v w b g a q x)-
      (q x+pathGenerator m v f q x+2*mixedDirectionSource m v w f a x+
        fderiv ℝ (fderiv ℝ g) x w w+mixedDirectionSource m v b f g x)| ≤
      C*(pathExpansionConstant B+3*(1+4*B)*(1+B)^2+secondNoiseBiasCoefficient B)*d^4 := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hv1 := hv.trans hd1
  have hweakq := abs_noiseMean_generator_remainder_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hq).potential le_rfl hm v x hv1
  have hJa := qBoundedJets_mixedDirectionSource_order (n := 1) hf ha hm v w
  have hJg := qBoundedJets_mixedDirectionSource_order (n := 1) hf hg hm v b
  have haweak := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hJa).potential (by norm_num) hm v x hv1
  have hgweak := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hJg).potential (by norm_num) hm v x hv1
  have hH := (hg.derivativeJets.derivativeJets.apply_const w).apply_const w
  have hHweak := abs_noise_second_weighted_sub_le hf3 hH hm v x hv1
  have hiq := integrable_tilted_shift hf (by norm_num) hq m v x
  have hia := (integrable_noise_test_powers hf3 ((ha.derivativeJets.apply_const w).of_le (by norm_num : 1 ≤ 3)) m v x).1
  have hib := (integrable_noise_test_powers hf3 ((hg.derivativeJets.apply_const b).of_le (by norm_num : 1 ≤ 3)) m v x).1
  have hiH := (integrable_noise_test_powers hf3 (hH.of_le (by norm_num : 1 ≤ 2)) m v x).2
  have hsplit : noiseMean m v f x (movingAverageTestSecond v w b g a q x) =
      tiltedAverage m v f q x+
      2*noiseMean m v f x (fun t => t*fderiv ℝ a (x+t • v) w)+
      noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)+
      noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) b) := by
    unfold noiseMean tiltedAverage movingAverageTestSecond
    rw [integral_add
      (f := fun t => q (x+t • v)+2*(t*fderiv ℝ a (x+t • v) w)+
        t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)
      (g := fun t => t*fderiv ℝ g (x+t • v) b) ((hiq.add (hia.const_mul 2)).add hiH) hib,
      integral_add (f := fun t => q (x+t • v)+2*(t*fderiv ℝ a (x+t • v) w))
        (g := fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w) (hiq.add (hia.const_mul 2)) hiH,
      integral_add (f := fun t => q (x+t • v))
        (g := fun t => 2*(t*fderiv ℝ a (x+t • v) w)) hiq (hia.const_mul 2),integral_const_mul]
  rw [hsplit,noise_mixedDirectionSource_c2 (hf.of_le (by norm_num : 2 ≤ 4))
    (ha.of_le (by norm_num : 2 ≤ 4)),
    noise_mixedDirectionSource_c2 (hf.of_le (by norm_num : 2 ≤ 4))
      (hg.of_le (by norm_num : 2 ≤ 4))]
  have hP := pathExpansionConstant_nonneg hB
  have hN : 0 ≤ secondNoiseBiasCoefficient B := by
    dsimp only [secondNoiseBiasCoefficient,defectNoiseMomentBound]
    positivity
  have he : tiltedAverage m v f q x+
      2*tiltedAverage m v f (mixedDirectionSource m v w f a) x+
      noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)+
      tiltedAverage m v f (mixedDirectionSource m v b f g) x-
      (q x+pathGenerator m v f q x+2*mixedDirectionSource m v w f a x+
        fderiv ℝ (fderiv ℝ g) x w w+mixedDirectionSource m v b f g x) =
      (tiltedAverage m v f q x-q x-pathGenerator m v f q x)+
      2*(tiltedAverage m v f (mixedDirectionSource m v w f a) x-mixedDirectionSource m v w f a x)+
      (noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)-
        fderiv ℝ (fderiv ℝ g) x w w)+
      (tiltedAverage m v f (mixedDirectionSource m v b f g) x-mixedDirectionSource m v b f g x) := by ring
  rw [he]
  have htri (u z y t : ℝ) : |u+2*z+y+t| ≤ |u|+2*|z|+|y|+|t| := by
    apply (abs_add_le _ _).trans
    apply add_le_add _ le_rfl
    apply (abs_add_le _ _).trans
    apply add_le_add _ le_rfl
    simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] using abs_add_le u (2*z)
  apply (htri _ _ _ _).trans
  calc
    _ ≤ C*pathExpansionConstant B*‖v‖^4+
        2*((1+4*B)*C*‖v‖*‖w‖*(1+B)^2*‖v‖^2)+
        (C*‖w‖*‖w‖)*secondNoiseBiasCoefficient B*‖v‖^2+
        (1+4*B)*C*‖v‖*‖b‖*(1+B)^2*‖v‖^2 := by
      apply add_le_add (add_le_add (add_le_add ?_ ?_) hHweak) ?_
      · simpa only [tiltedAverage,noiseMean,pathGenerator,sub_add_eq_sub_sub] using hweakq
      · simpa only [tiltedAverage,noiseMean,show (2:ℝ)^2 = 4 by norm_num] using
          mul_le_mul_of_nonneg_left haweak (by norm_num : (0:ℝ) ≤ 2)
      · simpa only [tiltedAverage,noiseMean,show (2:ℝ)^2 = 4 by norm_num] using hgweak
    _ ≤ C*pathExpansionConstant B*d^4+2*((1+4*B)*C*d*d*(1+B)^2*d^2)+
        (C*d*d)*secondNoiseBiasCoefficient B*d^2+(1+4*B)*C*d*d*(1+B)^2*d^2 := by gcongr
    _ = _ := by ring

def secondWeakCubicCoefficient (B A H : ℝ) : ℝ :=
  let J := 1+B+A+H
  let M₁ := defectNoiseMomentBound 1 B
  let M₂ := defectNoiseMomentBound 2 B
  let M₃ := defectNoiseMomentBound 3 B
  let W := pathExpansionConstant B+3*(1+4*B)*(1+B)^2+secondNoiseBiasCoefficient B
  W+43*J*(M₃+M₂*M₁)+21*J*(B+2*B^2)+
    9*J^2*((M₃+M₁*M₂)+2*M₁*(M₂+M₁^2))

theorem secondWeakCubicCoefficient_nonneg {B A H : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    0 ≤ secondWeakCubicCoefficient B A H := by
  have hP := pathExpansionConstant_nonneg hB
  dsimp only [secondWeakCubicCoefficient,secondNoiseBiasCoefficient,defectNoiseMomentBound]
  positivity

theorem abs_secondMovingAverageSource_sub_quadratic_cubic {B A H C d m dm ddm : ℝ}
    {f f₁ f₂ g a q : E → ℝ}
    (hf : QPotential 4 B f) (hf₁ : QBoundedJets 3 A f₁) (hf₂ : QBoundedJets 2 H f₂)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 C a) (hq : QBoundedJets 4 C q)
    (hm : m ∈ Icc (0:ℝ) 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (v w b x : E)
    (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) :
    |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x-
      secondMovingAverageQuadratic m dm ddm v w b f f₁ f₂ g a q x| ≤
      C*secondWeakCubicCoefficient B A H*d^3 := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have hH := hf₂.nonneg
  have hC := hg.nonneg
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
  let J := 1+B+A+H
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hS : 2*B+A ≤ 3*J := by dsimp only [J]; linarith
  have hT : 4*B+4*A+H ≤ 9*J := by dsimp only [J]; linarith
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf3 (by norm_num) m v x
  let G : ℝ → ℝ := fun t => g (x+t • v)
  let T := movingAverageTestFirst v w g a x
  let S := firstAverageScore m dm v w f f₁ x
  let U := secondAverageScoreLinear m dm ddm v w b f f₁ f₂ x
  let V := secondAverageScoreQuadratic m v w f x
  let R : ℝ → ℝ := fun t => U t+V t
  let tg := fderiv ℝ g x v
  let ta := fderiv ℝ a x v+fderiv ℝ g x w
  let ts := dm*fderiv ℝ f x v+m*(fderiv ℝ f₁ x v+fderiv ℝ f x w)
  let tt := ddm*fderiv ℝ f x v+2*dm*(fderiv ℝ f₁ x v+fderiv ℝ f x w)+
    m*(fderiv ℝ f₂ x v+2*fderiv ℝ f₁ x w+fderiv ℝ f x b)
  let P := q x+pathGenerator m v f q x+2*mixedDirectionSource m v w f a x+
    fderiv ℝ (fderiv ℝ g) x w w+mixedDirectionSource m v b f g x
  let W := pathExpansionConstant B+3*(1+4*B)*(1+B)^2+secondNoiseBiasCoefficient B
  let M₁ := defectNoiseMomentBound 1 B
  let M₂ := defectNoiseMomentBound 2 B
  let M₃ := defectNoiseMomentBound 3 B
  have hW : 0 ≤ W := by
    have hP := pathExpansionConstant_nonneg hB
    dsimp only [W,secondNoiseBiasCoefficient,defectNoiseMomentBound]
    positivity
  have hline : Continuous (fun t : ℝ => x+t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hgc (t : ℝ) : |G t| ≤ C := by
    simpa only [G,Real.norm_eq_abs] using hg.norm_le (x+t • v)
  have hgc' (t : ℝ) : |G t-g x| ≤ C*d*|t| := by
    have H' := (qBoundedJets_movingTest_centered (hg.of_le (by norm_num : 1 ≤ 4)) v t).norm_le x
    simp only [Real.norm_eq_abs] at H'
    exact H'.trans (by gcongr)
  have htc' (t : ℝ) : |T t-a x| ≤ (2*C)*d*|t| := by
    have H' := (qBoundedJets_movingTestFirst_centered (hg.of_le (by norm_num : 1 ≤ 4))
      (ha.of_le (by norm_num : 1 ≤ 4)) v w t).norm_le x
    simp only [Real.norm_eq_abs] at H'
    apply H'.trans
    calc
      _ ≤ (C*d+C*d)*|t| := by gcongr
      _ = _ := by ring
  have hscore := averageScore_envelopes hf3 (hf₁.of_le (by norm_num : 1 ≤ 3))
    (hf₂.of_le (by norm_num : 1 ≤ 2)) hm hdm hddm hd v w b hv hw hb x
  have hsc (t : ℝ) : |S t| ≤ (3*J)*d*|t| :=
    (hscore t).1.trans (by gcongr)
  have huc (t : ℝ) : |U t| ≤ (9*J)*d*|t| :=
    (hscore t).2.1.trans (by gcongr)
  have hvc (t : ℝ) : |V t| ≤ B*d^2*|t|^2 := (hscore t).2.2
  have hfc := hf.smooth.continuous
  have hf₁c := hf₁.smooth.continuous
  have hf₂c := hf₂.smooth.continuous
  have hac := ha.smooth.continuous
  have hdf := hf.smooth.continuous_fderiv (by norm_num)
  have hddf := (hf.smooth.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hdf₁ := hf₁.smooth.continuous_fderiv (by norm_num)
  have hdg := hg.smooth.continuous_fderiv (by norm_num)
  have hGcont : Continuous G := hg.smooth.continuous.comp hline
  have hTcont : Continuous T := by
    change Continuous (fun t : ℝ => a (x+t • v)+t*fderiv ℝ g (x+t • v) w)
    fun_prop
  have hScont : Continuous S := by
    change Continuous (fun t : ℝ => dm*(f (x+t • v)-f x)+
      m*(f₁ (x+t • v)-f₁ x+t*fderiv ℝ f (x+t • v) w))
    fun_prop
  have hUcont : Continuous U := by
    change Continuous (fun t : ℝ => ddm*(f (x+t • v)-f x)+
      2*dm*(f₁ (x+t • v)-f₁ x+t*fderiv ℝ f (x+t • v) w)+
      m*(f₂ (x+t • v)-f₂ x+2*(t*fderiv ℝ f₁ (x+t • v) w)+t*fderiv ℝ f (x+t • v) b))
    fun_prop
  have hVcont : Continuous V := by
    change Continuous (fun t : ℝ => m*t^2*fderiv ℝ (fderiv ℝ f) (x+t • v) w w)
    fun_prop
  have hGmem : MemLp G 2 μ := memLp_step_noise_of_polynomial_bound hf3 m v x 0
    hGcont hC (by simpa only [pow_zero,mul_one] using hgc)
  have hTmem : MemLp T 2 μ := by
    have H' := memLp_step_noise_of_polynomial_bound hf3 m v x 1
      (hTcont.sub continuous_const) (by positivity : 0 ≤ (2*C)*d)
      (by simpa only [pow_one,Pi.sub_apply] using htc')
    convert H'.add (memLp_const (a x)) using 1
    funext t
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  have hSmem : MemLp S 2 μ := memLp_step_noise_of_polynomial_bound hf3 m v x 1
    hScont (by positivity : 0 ≤ (3*J)*d) (by simpa only [pow_one] using hsc)
  have hUmem : MemLp U 2 μ := memLp_step_noise_of_polynomial_bound hf3 m v x 1
    hUcont (by positivity : 0 ≤ (9*J)*d) (by simpa only [pow_one] using huc)
  have hVmem : MemLp V 2 μ := memLp_step_noise_of_polynomial_bound hf3 m v x 2
    hVcont (by positivity : 0 ≤ B*d^2) hvc
  have hRmem : MemLp R 2 μ := hUmem.add hVmem
  have hSSmem : MemLp (fun t => S t^2) 2 μ := memLp_step_noise_of_polynomial_bound hf3 m v x 2
    (hScont.pow 2) (sq_nonneg ((3*J)*d)) (by
      intro t
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hsc t) 2).trans_eq (by ring))
  have himem : MemLp (fun t : ℝ => t) 2 μ := memLp_step_noise_of_polynomial_bound (K := 1) hf3 m v x 1
    continuous_id (by norm_num) (by intro t; simp only [pow_one,one_mul,le_refl])
  have hgp := (qBoundedJets_iff_qBddSmooth.mp hg).potential
  have hap := (qBoundedJets_iff_qBddSmooth.mp ha).potential
  have htg : |tg| ≤ C*d := (hgp.directional_le (by norm_num) x v).trans (by gcongr)
  have hta : |ta| ≤ (2*C)*d := by
    calc
      _ ≤ |fderiv ℝ a x v|+|fderiv ℝ g x w| := abs_add_le _ _
      _ ≤ C*‖v‖+C*‖w‖ := add_le_add (hap.directional_le (by norm_num) x v)
        (hgp.directional_le (by norm_num) x w)
      _ ≤ (2*C)*d := by nlinarith [mul_le_mul_of_nonneg_left hv hC,mul_le_mul_of_nonneg_left hw hC]
  have hts : |ts| ≤ (3*J)*d :=
    (abs_firstAverageScore_tangent_le hf3 hf₁ hmabs hdm v w x hv hw).trans (by gcongr)
  have htt : |tt| ≤ (9*J)*d :=
    (abs_secondAverageScore_tangent_le hf3 hf₁ hf₂ hmabs hdm hddm v w b x hv hw hb).trans (by gcongr)
  have hgr (t : ℝ) : |G t-g x-tg*t| ≤ C*d^2*|t|^2 := by
    have H' := abs_potential_noise_linear_remainder (hgp.of_le (by norm_num : 2 ≤ 4)) v x t
    dsimp only [G,tg]
    rw [mul_comm (fderiv ℝ g x v) t]
    exact H'.trans (by gcongr)
  have har (t : ℝ) : |T t-a x-ta*t| ≤ (2*C)*d^2*|t|^2 := by
    have H' := abs_movingTestFirst_sub_tangent (hg.of_le (by norm_num : 3 ≤ 4))
      (ha.of_le (by norm_num : 2 ≤ 4)) hd v w x hv hw t
    dsimp only [T,ta]
    convert H' using 1 <;> congr 1 <;> ring
  have hsr (t : ℝ) : |S t-ts*t| ≤ (3*J)*d^2*|t|^2 := by
    have H' := abs_firstAverageScore_sub_tangent (m := m) (dm := dm)
      hf3 (hf₁.of_le (by norm_num : 2 ≤ 3)) hd v w x hv hw t
    have hc : |dm| *B+|m| *(A+B) ≤ 3*J := by
      calc
        _ ≤ 1*B+1*(A+B) := by gcongr
        _ ≤ 3*J := by dsimp only [J]; linarith
    convert H'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (sq_nonneg d)) (sq_nonneg |t|)) using 1
    congr 1
    dsimp only [S,ts]
    ring
  have htr (t : ℝ) : |R t-tt*t| ≤ (10*J)*d^2*|t|^2 := by
    have H' := abs_secondAverageScore_sub_tangent (m := m) (dm := dm) (ddm := ddm)
      hf3 hf₁ hf₂ hd v w b x hv hw hb t
    have hc : |ddm| *B+2*|dm| *(A+B)+|m| *(H+2*A+2*B) ≤ 10*J := by
      calc
        _ ≤ 1*B+2*1*(A+B)+1*(H+2*A+2*B) := by gcongr
        _ ≤ 10*J := by dsimp only [J]; linarith
    convert H'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (sq_nonneg d)) (sq_nonneg |t|)) using 1
    congr 1
    dsimp only [R,U,V,tt]
    ring
  have hvar : |covariance (fun t : ℝ => t) (fun t : ℝ => t) μ-1| ≤ (B+2*B^2)*d := by
    apply (abs_step_noise_variance_sub_one_le hf3 hm v x).trans
    have hd2 : d^2 ≤ d := by nlinarith only [mul_nonneg hd (sub_nonneg.mpr hd1)]
    gcongr
    exact (pow_le_pow_left₀ (norm_nonneg _) hv 2).trans hd2
  have havg := abs_noise_movingTestSecond_sub_quadratic_le hf hg ha hq hm hd hd1 v w b x hv hw hb
  have H' := abs_secondAverageTransport_sub_tangents_le hGmem hTmem hSmem hRmem hSSmem himem
    hC hJ hW hd hd1 hgc' hsc htg hta hts htt hgr har hsr htr
    (by simpa only [pow_one] using integrable_step_noise_abs_power hf3 m v x 1)
    (integrable_step_noise_abs_power hf3 m v x 2)
    (integrable_step_noise_abs_power hf3 m v x 3)
    (by simpa only [pow_one,noiseMean,μ] using noise_abs_moment_le hf3 hm v x (hv.trans hd1) 1)
    (noise_abs_moment_le hf3 hm v x (hv.trans hd1) 2)
    (noise_abs_moment_le hf3 hm v x (hv.trans hd1) 3) hvar havg
  convert H' using 1
  · congr 1
    dsimp only [secondMovingAverageSource,secondMovingAverageQuadratic,G,T,S,R,U,V,P,tg,ta,ts,tt,μ]
    ring
  · dsimp only [secondWeakCubicCoefficient,J,M₁,M₂,M₃,W]

theorem eventually_mesh_cubic_energy_le {K C L h eps : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hh : 0 ≤ h) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ e : ℝ, 0 ≤ e → e ≤ L*h/(N:ℝ) →
      Real.sqrt e ≤ 1 ∧
        (C*h/(N:ℝ))*K*(Real.sqrt e)^3 ≤ (eps/(N:ℝ))*e := by
  have hlim : Tendsto (fun N : ℕ => L*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (L*h/(N:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  have hcoef : Tendsto (fun N : ℕ => C*h*K*Real.sqrt (L*h/(N:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hsqrt
  have hsmall : ∀ᶠ N : ℕ in atTop, L*h/(N:ℝ) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hco : ∀ᶠ N : ℕ in atTop, C*h*K*Real.sqrt (L*h/(N:ℝ)) < eps :=
    hcoef.eventually (gt_mem_nhds heps)
  filter_upwards [hsmall,hco] with N hN hCN
  intro e he0 he
  refine ⟨Real.sqrt_le_one.mpr (he.trans hN.le),?_⟩
  have hCe : C*h*K*Real.sqrt e ≤ eps := by
    apply le_trans _ hCN.le
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by positivity)
  have he3 : (Real.sqrt e)^3 = Real.sqrt e*e := by
    calc
      _ = Real.sqrt e*(Real.sqrt e)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt he0]
  calc
    _ = ((C*h*K*Real.sqrt e)/(N:ℝ))*e := by rw [he3]; ring
    _ ≤ (eps/(N:ℝ))*e := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hCe (Nat.cast_nonneg N)) he0

end SKBarriers2.StepCalculus
