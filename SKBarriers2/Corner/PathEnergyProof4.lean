module

public import SKBarriers2.Corner.PathEnergyProof3
public import SKBarriers2.Analysis.GaussianTaylor

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

def movingAverageTestFirst (v w : E) (g a : E → ℝ) (x : E) (t : ℝ) : ℝ :=
  a (x+t • v) + t*fderiv ℝ g (x+t • v) w

def movingAverageTestSecond (v w b : E) (g a q : E → ℝ) (x : E) (t : ℝ) : ℝ :=
  q (x+t • v) + 2*(t*fderiv ℝ a (x+t • v) w) +
    t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w + t*fderiv ℝ g (x+t • v) b

theorem qBoundedJets_movingTest_centered {n : ℕ} {C : ℝ} {g : E → ℝ}
    (hg : QBoundedJets (n+1) C g) (v : E) (t : ℝ) :
    QBoundedJets n (C*‖v‖*|t|) (fun x => g (x+t • v)-g x) := by
  have H := (qBoundedJets_iff_qBddSmooth.mp hg).potential.increment (t • v)
  convert H using 1
  rw [norm_smul,Real.norm_eq_abs]
  ring

theorem qBoundedJets_movingTestFirst_centered {n : ℕ} {C D : ℝ} {g a : E → ℝ}
    (hg : QBoundedJets (n+1) C g) (ha : QBoundedJets (n+1) D a)
    (v w : E) (t : ℝ) :
    QBoundedJets n ((D*‖v‖+C*‖w‖)*|t|)
      (fun x => movingAverageTestFirst v w g a x t-a x) := by
  have hA := qBoundedJets_movingTest_centered ha v t
  have hD := ((hg.derivativeJets.apply_const w).translate (t • v)).const_smul t
  convert hA.add hD using 1
  · ring
  · funext x
    simp only [movingAverageTestFirst,smul_eq_mul]
    ring

theorem qBoundedJets_movingTestSecond_remainder {n : ℕ} {C D : ℝ} {g a : E → ℝ}
    (hg : QBoundedJets (n+2) C g) (ha : QBoundedJets (n+1) D a)
    (v w b : E) (q : E → ℝ) (t : ℝ) :
    QBoundedJets n ((2*D*‖w‖+C*‖b‖)*|t|+C*‖w‖^2*|t|^2)
      (fun x => movingAverageTestSecond v w b g a q x t-q (x+t • v)) := by
  have hA := ((ha.derivativeJets.apply_const w).translate (t • v)).const_smul (2*t)
  have hH := (((hg.derivativeJets.derivativeJets.apply_const w).apply_const w).translate
    (t • v)).const_smul (t^2)
  have hD := ((((hg.derivativeJets.of_le (by omega : n ≤ n+1)).apply_const b).translate
    (t • v))).const_smul t
  convert (hA.add hH).add hD using 1
  · rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_pow,sq_abs]
    ring
  · funext x
    simp only [movingAverageTestSecond,smul_eq_mul]
    ring

theorem noise_mixedDirectionSource_c2 {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 2 B f) (hg : QBoundedJets 2 C g) (m : ℝ) (v w x : E) :
    noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) w) =
      tiltedAverage m v f (mixedDirectionSource m v w f g) x := by
  have hD := hg.derivativeJets.apply_const w
  have hH := (hg.derivativeJets.derivativeJets.apply_const v).apply_const w
  have hV := hf.derivativeJets.apply_const v
  have hd (t : ℝ) : HasDerivAt (fun a : ℝ => fderiv ℝ g (x+a • v) w)
      (fderiv ℝ (fderiv ℝ g) (x+t • v) v w) t := by
    have hline : HasDerivAt (fun a : ℝ => x+a • v) v t := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
    have H := (((hg.smooth.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (x+t • v)).hasFDerivAt.comp_hasDerivAt t hline).clm_apply
        (hasDerivAt_const t w)
    simpa only [Function.comp_def,map_zero,add_zero] using H
  have hc : Continuous (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (x+t • v) v w) :=
    hH.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hG : HasExpGrowth (fun t : ℝ => fderiv ℝ g (x+t • v) w) :=
    HasExpGrowth.of_bounded hD.nonneg (fun t => hD.norm_le _)
  have hG' : HasExpGrowth (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (x+t • v) v w) :=
    HasExpGrowth.of_bounded hH.nonneg (fun t => hH.norm_le _)
  have hiH := integrable_tilted_shift hf le_rfl hH m v x
  have hiP := integrable_tilted_shift hf le_rfl (hD.mul hV) m v x
  rw [tilted_integration_by_parts hf le_rfl m v x hd hc hG hG']
  unfold tiltedAverage mixedDirectionSource noiseMean
  rw [← integral_const_mul,← integral_add hiH (hiP.const_mul m)]

theorem abs_noise_directionalTest_le {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 2 B f) (hg : QBoundedJets 2 C g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v w x : E) :
    |noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) w)| ≤
      (1+B)*C*‖v‖*‖w‖ := by
  rw [noise_mixedDirectionSource_c2 hf hg]
  have hgp := (qBoundedJets_iff_qBddSmooth.mp hg).potential
  change |noiseMean m v f x (fun t => mixedDirectionSource m v w f g (x+t • v))| ≤ _
  apply abs_noiseMean_le hf le_rfl
  intro t
  unfold mixedDirectionSource
  have hB := hf.nonneg
  have hC := hg.nonneg
  have hprod : |m*(fderiv ℝ g (x+t • v) w*fderiv ℝ f (x+t • v) v)| ≤
      C*B*‖v‖*‖w‖ := by
    rw [abs_mul,abs_mul,abs_of_nonneg hm.1]
    calc
      _ ≤ 1*((C*‖w‖)*(B*‖v‖)) := by
        gcongr
        · exact hm.2
        · exact hgp.directional_le (by norm_num) _ w
        · exact hf.directional_le (by norm_num) _ v
      _ = _ := by ring
  exact (abs_add_le _ _).trans ((add_le_add
    (hgp.second_directional_le le_rfl (x+t • v) v w) hprod).trans_eq (by ring))

private theorem test_noise_integrable {B : ℝ} {f : E → ℝ} (hf : QPotential 3 B f)
    {C : ℝ} {g : E → ℝ} (hg : QBoundedJets 0 C g) (m : ℝ) (v x : E) (p : ℕ) :
    Integrable (fun t : ℝ => t^p*g (x+t • v)) (stepLaw m v f x) := by
  have hc : Continuous (fun t : ℝ => g (x+t • v)) :=
    hg.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hG : HasExpGrowth (fun t : ℝ => g (x+t • v)) :=
    HasExpGrowth.of_bounded hg.nonneg (fun t => hg.norm_le _)
  have hpow : HasExpGrowth (fun t : ℝ => t^p) := by
    simpa only [ContinuousLinearMap.id_apply] using (HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).pow p
  exact integrable_noise hf (by norm_num) m v x (hpow.mul hG) ((continuous_id.pow p).mul hc)

private theorem integral_four_terms {μ : Measure ℝ} {q a h b : ℝ → ℝ}
    (hq : Integrable q μ) (ha : Integrable a μ) (hh : Integrable h μ) (hb : Integrable b μ) :
    (∫ t, q t+2*a t+h t+b t ∂μ) =
      (∫ t, q t ∂μ)+2*(∫ t, a t ∂μ)+(∫ t, h t ∂μ)+(∫ t, b t ∂μ) := by
  have hqa : Integrable (fun t => q t+2*a t) μ := hq.add (ha.const_mul 2)
  have hqah : Integrable (fun t => q t+2*a t+h t) μ := hqa.add hh
  rw [integral_add (f := fun t => q t+2*a t+h t) (g := b) hqah hb,
    integral_add (f := fun t => q t+2*a t) (g := h) hqa hh,
    integral_add (f := q) (g := fun t => 2*a t) hq (ha.const_mul 2),integral_const_mul]

set_option maxHeartbeats 800000 in
theorem abs_noise_movingTestSecond_le {B C D H : ℝ} {f g a q : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 2 C g)
    (ha : QBoundedJets 2 D a) (hq : QBoundedJets 0 H q)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v w b x : E) (hv : ‖v‖ ≤ 1) :
    |noiseMean m v f x (movingAverageTestSecond v w b g a q x)| ≤
      H+2*(1+B)*D*‖v‖*‖w‖+(1+B)*C*‖v‖*‖b‖+
        defectNoiseMomentBound 2 B*C*‖w‖^2 := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  have hD := ha.nonneg
  have hH := hq.nonneg
  have hqI := integrable_tilted_shift hf (by norm_num) hq m v x
  have haI := test_noise_integrable hf
    ((ha.derivativeJets.apply_const w).of_le (by norm_num : 0 ≤ 1)) m v x 1
  have hgI := test_noise_integrable hf
    ((hg.derivativeJets.apply_const b).of_le (by norm_num : 0 ≤ 1)) m v x 1
  have hhess := (hg.derivativeJets.derivativeJets.apply_const w).apply_const w
  have hhI := test_noise_integrable hf hhess m v x 2
  simp only [pow_one] at haI hgI
  have hqB : |noiseMean m v f x (fun t => q (x+t • v))| ≤ H :=
    abs_noiseMean_le hf (by norm_num) m v x (fun t => by
      simpa only [Real.norm_eq_abs] using hq.norm_le (x+t • v))
  have haB := abs_noise_directionalTest_le (hf.of_le (by norm_num)) ha hm v w x
  have hgB := abs_noise_directionalTest_le (hf.of_le (by norm_num)) hg hm v b x
  have hmoment : Integrable (fun t : ℝ => |t|^2) (stepLaw m v f x) := by
    have H := test_noise_integrable hf
      (C := 1) (g := fun _ : E => (1 : ℝ)) ⟨by norm_num,contDiff_const,by
        intro j hj y
        have hj0 : j=0 := by omega
        subst j
        norm_num [norm_iteratedFDeriv_zero]⟩ m v x 2
    simpa only [sq_abs,mul_one] using H
  have hhB : |noiseMean m v f x
      (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)| ≤
        (C*‖w‖*‖w‖)*defectNoiseMomentBound 2 B := by
    apply abs_integral_le_noise_moment hmoment (by positivity)
    · intro t
      rw [abs_mul,abs_pow]
      exact (mul_le_mul_of_nonneg_left (show
        |fderiv ℝ (fderiv ℝ g) (x+t • v) w w| ≤ C*‖w‖*‖w‖ from
          by simpa only [Real.norm_eq_abs] using hhess.norm_le (x+t • v))
        (sq_nonneg |t|)).trans_eq (by ring)
    · exact noise_abs_moment_le hf hm v x hv 2
  have he : noiseMean m v f x (movingAverageTestSecond v w b g a q x) =
      noiseMean m v f x (fun t => q (x+t • v))+
        2*noiseMean m v f x (fun t => t*fderiv ℝ a (x+t • v) w)+
        noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)+
        noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) b) := by
    unfold movingAverageTestSecond noiseMean
    exact integral_four_terms hqI haI hhI hgI
  rw [he]
  have htri : |noiseMean m v f x (fun t => q (x+t • v))+
        2*noiseMean m v f x (fun t => t*fderiv ℝ a (x+t • v) w)+
        noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)+
        noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) b)| ≤
      |noiseMean m v f x (fun t => q (x+t • v))|+
        2*|noiseMean m v f x (fun t => t*fderiv ℝ a (x+t • v) w)|+
        |noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w)|+
        |noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) b)| := by
    have H (r s t u : ℝ) : |r+s+t+u| ≤ |r|+|s|+|t|+|u| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using H
      (noiseMean m v f x (fun t => q (x+t • v)))
      (2*noiseMean m v f x (fun t => t*fderiv ℝ a (x+t • v) w))
      (noiseMean m v f x (fun t => t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w))
      (noiseMean m v f x (fun t => t*fderiv ℝ g (x+t • v) b))
  exact htri.trans ((add_le_add (add_le_add (add_le_add hqB
    (mul_le_mul_of_nonneg_left haB (by norm_num : (0 : ℝ) ≤ 2))) hhB) hgB).trans_eq (by ring))

def secondMovingAverageSource (m dm ddm : ℝ) (v w b : E)
    (f f₁ f₂ g a q : E → ℝ) (x : E) : ℝ :=
  secondAverageTransport (stepLaw m v f x)
    (fun t => g (x+t • v)) (movingAverageTestFirst v w g a x)
    (movingAverageTestSecond v w b g a q x) (firstAverageScore m dm v w f f₁ x)
    (fun t => secondAverageScoreLinear m dm ddm v w b f f₁ f₂ x t+
      secondAverageScoreQuadratic m v w f x t)

private theorem transport_noise_memLp {B K : ℝ} {f : E → ℝ}
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

private theorem transport_noise_moment_integrable {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (m : ℝ) (v x : E) (p : ℕ) :
    Integrable (fun t : ℝ => |t|^p) (stepLaw m v f x) := by
  have hpow : HasExpGrowth (fun t : ℝ => t^p) := by
    simpa only [ContinuousLinearMap.id_apply] using
      (HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).pow p
  have hnorm := hpow.norm (fun t => norm_nonneg (t^p))
  have habs : HasExpGrowth (fun t : ℝ => |t|^p) := by
    simpa only [Real.norm_eq_abs,abs_pow] using hnorm
  exact integrable_noise hf (by norm_num) m v x habs (continuous_abs.pow p)

def secondMovingAverageScale (B A H : ℝ) : ℝ :=
  4*B+4*A+H+3*(1+B)+defectNoiseMomentBound 2 B

theorem abs_secondMovingAverageSource_le {B A H C D Q d m dm ddm : ℝ}
    {f f₁ f₂ g a q : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 1 A f₁) (hf₂ : QBoundedJets 1 H f₂)
    (hg : QBoundedJets 2 C g) (ha : QBoundedJets 2 D a) (hq : QBoundedJets 0 Q q)
    (hm : m ∈ Icc (0 : ℝ) 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (v w b : E)
    (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hb : ‖b‖ ≤ d) (x : E) :
    |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x| ≤
      Q+secondAverageTransportCoefficient (secondMovingAverageScale B A H)
        (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B)
        (defectNoiseMomentBound 3 B)*(C+D)*d^2 := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have hH := hf₂.nonneg
  have hC := hg.nonneg
  have hD := ha.nonneg
  have hQ := hq.nonneg
  let M₁ := defectNoiseMomentBound 1 B
  let M₂ := defectNoiseMomentBound 2 B
  let M₃ := defectNoiseMomentBound 3 B
  let R := secondMovingAverageScale B A H
  have hM₁ : 0 ≤ M₁ := abs_nonneg _
  have hM₂ : 0 ≤ M₂ := abs_nonneg _
  have hM₃ : 0 ≤ M₃ := abs_nonneg _
  have hR : 0 ≤ R := by dsimp only [R,secondMovingAverageScale]; positivity
  let μ := stepLaw m v f x
  let G : ℝ → ℝ := fun t => g (x+t • v)
  let T := movingAverageTestFirst v w g a x
  let S := firstAverageScore m dm v w f f₁ x
  let U := secondAverageScoreLinear m dm ddm v w b f f₁ f₂ x
  let V := secondAverageScoreQuadratic m v w f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hgc (t : ℝ) : |G t| ≤ C := by
    simpa only [G,Real.norm_eq_abs] using hg.norm_le (x+t • v)
  have hGcenter := qBoundedJets_movingTest_centered (hg.of_le (by norm_num : 1 ≤ 2)) v
  have hTcenter := qBoundedJets_movingTestFirst_centered
    (hg.of_le (by norm_num : 1 ≤ 2)) (ha.of_le (by norm_num : 1 ≤ 2)) v w
  have hgc' (t : ℝ) : |G t-g x| ≤ (C*d)*|t| := by
    have H := hGcenter t |>.norm_le x
    simp only [Real.norm_eq_abs] at H
    exact H.trans (by gcongr)
  have htc' (t : ℝ) : |T t-a x| ≤ ((C+D)*d)*|t| := by
    have H := hTcenter t |>.norm_le x
    simp only [Real.norm_eq_abs] at H
    calc
      _ ≤ (D*‖v‖+C*‖w‖)*|t| := H
      _ ≤ (D*d+C*d)*|t| := by gcongr
      _ = _ := by ring
  have hscore := averageScore_envelopes hf hf₁ hf₂ hm hdm hddm hd v w b hv hw hb x
  have hs (t : ℝ) : |S t| ≤ ((2*B+A)*d)*|t| := (hscore t).1
  have hu (t : ℝ) : |U t| ≤ ((4*B+4*A+H)*d)*|t| := (hscore t).2.1
  have hvv (t : ℝ) : |V t| ≤ (B*d^2)*|t|^2 := (hscore t).2.2
  have hline : Continuous (fun t : ℝ => x+t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hfc := hf.smooth.continuous
  have hf₁c := hf₁.smooth.continuous
  have hf₂c := hf₂.smooth.continuous
  have hac := ha.smooth.continuous
  have hdf : Continuous (fderiv ℝ f) := hf.smooth.continuous_fderiv (by norm_num)
  have hddf : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.smooth.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hdf₁ : Continuous (fderiv ℝ f₁) := hf₁.smooth.continuous_fderiv (by norm_num)
  have hsc : Continuous S := by
    change Continuous (fun t : ℝ => firstAverageScore m dm v w f f₁ x t)
    unfold firstAverageScore
    fun_prop
  have huc : Continuous U := by
    change Continuous (fun t : ℝ => secondAverageScoreLinear m dm ddm v w b f f₁ f₂ x t)
    unfold secondAverageScoreLinear
    fun_prop
  have hvc : Continuous V := by
    change Continuous (fun t : ℝ => secondAverageScoreQuadratic m v w f x t)
    unfold secondAverageScoreQuadratic
    fun_prop
  have hgm : MemLp G 2 μ := transport_noise_memLp hf m v x 0
    (hg.smooth.continuous.comp hline) hC (by simpa only [pow_zero,mul_one] using hgc)
  have htm0 : MemLp (fun t => T t-a x) 2 μ :=
    transport_noise_memLp (K := (C+D)*d) hf m v x 1
    (by
      have H : Continuous (fun t : ℝ => movingAverageTestFirst v w g a x t-a x) := by
        have hdg := hg.smooth.continuous_fderiv (by norm_num)
        dsimp only [movingAverageTestFirst]
        fun_prop
      exact H) (by positivity) (by simpa only [pow_one] using htc')
  have htm : MemLp T 2 μ := by
    convert htm0.add (memLp_const (a x)) using 1
    funext t
    simp only [Pi.add_apply]
    ring
  have hsm : MemLp S 2 μ := transport_noise_memLp (K := (2*B+A)*d) hf m v x 1 hsc (by positivity)
    (by simpa only [pow_one] using hs)
  have hum : MemLp U 2 μ := transport_noise_memLp (K := (4*B+4*A+H)*d) hf m v x 1 huc (by positivity)
    (by simpa only [pow_one] using hu)
  have hvm : MemLp V 2 μ := transport_noise_memLp (K := B*d^2) hf m v x 2 hvc (by positivity) hvv
  have hssm : MemLp (fun t => S t^2) 2 μ := transport_noise_memLp (K := ((2*B+A)*d)^2) hf m v x 2
    (hsc.pow 2) (sq_nonneg _) (by
      intro t
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hs t) 2).trans_eq (by ring))
  have htop := abs_noise_movingTestSecond_le hf hg ha hq hm v w b x (hv.trans hd1)
  have htop' : |noiseMean m v f x (movingAverageTestSecond v w b g a q x)| ≤
      Q+R*(C+D)*d^2 := by
    have hcoef : 2*(1+B)*D+(1+B)*C+M₂*C ≤ R*(C+D) := by
      have H : 0 ≤ (4*B+4*A+H)*(C+D)+2*(1+B)*C+(1+B)*D+M₂*D := by positivity
      dsimp only [R,secondMovingAverageScale,M₂] at *
      nlinarith only [H]
    calc
      _ ≤ Q+2*(1+B)*D*‖v‖*‖w‖+(1+B)*C*‖v‖*‖b‖+M₂*C*‖w‖^2 := htop
      _ ≤ Q+2*(1+B)*D*d*d+(1+B)*C*d*d+M₂*C*d^2 := by gcongr
      _ = Q+(2*(1+B)*D+(1+B)*C+M₂*C)*d^2 := by ring
      _ ≤ Q+R*(C+D)*d^2 := by gcongr
  have hmain := abs_secondAverageTransport_le hgm htm hsm hum hvm hssm
    hC (show 0 ≤ C*d by positivity) (show 0 ≤ (C+D)*d by positivity)
    (show 0 ≤ (2*B+A)*d by positivity) (show 0 ≤ (4*B+4*A+H)*d by positivity)
    (show 0 ≤ B*d^2 by positivity) hgc hgc' htc' hs hu hvv
    (by simpa only [pow_one] using transport_noise_moment_integrable hf m v x 1)
    (transport_noise_moment_integrable hf m v x 2)
    (transport_noise_moment_integrable hf m v x 3)
    (by simpa only [pow_one,noiseMean,μ] using noise_abs_moment_le hf hm v x (hv.trans hd1) 1)
    (noise_abs_moment_le hf hm v x (hv.trans hd1) 2)
    (noise_abs_moment_le hf hm v x (hv.trans hd1) 3) htop'
  have hScoef : 2*B+A ≤ R := by dsimp only [R,secondMovingAverageScale]; linarith
  have hTcoef : 4*B+4*A+H ≤ R := by
    dsimp only [R,secondMovingAverageScale]
    linarith
  have hUcoef : B ≤ R := by dsimp only [R,secondMovingAverageScale]; linarith
  have hbudget := secondAverageTransport_budget_le (H := Q) hC hD (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hR hd hd1 hM₁ hM₂ hM₃
    (le_refl (C*d)) (le_refl ((C+D)*d))
    (mul_le_mul_of_nonneg_right hScoef hd) (mul_le_mul_of_nonneg_right hTcoef hd)
    (mul_le_mul_of_nonneg_right hUcoef (sq_nonneg d))
  exact hmain.trans hbudget

end SKBarriers2.StepCalculus

namespace SKBarriers2.QBoundedJets

section SpatialInterpolation

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_fderiv_le_of_value_bound {A B t : ℝ} {f : X → Y}
    (hf : QBoundedJets 2 B f) (hA : 0 ≤ A) (hv : ∀ x, ‖f x‖ ≤ A)
    (ht : 0 < t) (x : X) :
    ‖fderiv ℝ f x‖ ≤ 2*A/t+B*t := by
  have hB := hf.nonneg
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  have hTaylor := hf.linear_taylor_remainder_le x (t • w)
  have hrem : ‖f (x+t • w)-f x-fderiv ℝ f x (t • w)‖ ≤ B*t^2 := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos ht,hw,mul_one] using hTaylor
  have he : t • (fderiv ℝ f x w) =
      (f (x+t • w)-f x)-(f (x+t • w)-f x-fderiv ℝ f x (t • w)) := by
    rw [map_smul]
    module
  have H : t*‖fderiv ℝ f x w‖ ≤ 2*A+B*t^2 := by
    calc
      _ = ‖t • (fderiv ℝ f x w)‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      _ ≤ ‖f (x+t • w)-f x‖+‖f (x+t • w)-f x-fderiv ℝ f x (t • w)‖ := by
        rw [he]
        exact norm_sub_le _ _
      _ ≤ (A+A)+B*t^2 := add_le_add ((norm_sub_le _ _).trans
        (add_le_add (hv _) (hv _))) hrem
      _ = _ := by ring
  have heq : t*(2*A/t+B*t) = 2*A+B*t^2 := by field_simp
  apply le_of_not_gt
  intro hbad
  have Hbad := mul_lt_mul_of_pos_left hbad ht
  rw [heq] at Hbad
  linarith only [H,Hbad]

theorem interpolate_succ {r : ℕ} {A B t : ℝ} {f : X → Y}
    (hhigh : QBoundedJets (r+2) B f) (hlow : QBoundedJets r A f)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    QBoundedJets (r+1) (3*A/t+B*t) f := by
  have hA := hlow.nonneg
  have hB := hhigh.nonneg
  refine ⟨by positivity,hhigh.smooth.of_le (by exact_mod_cast (show r+1 ≤ r+2 by omega)),?_⟩
  intro j hj x
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have H : A ≤ 3*A/t := (le_div_iff₀ ht).mpr (by nlinarith only [hA,mul_le_of_le_one_right hA ht1])
    exact (hlow.norm_le x).trans (H.trans (le_add_of_nonneg_right (by positivity)))
  | succ j =>
    rw [← norm_fderiv_iteratedFDeriv]
    have hh : QBoundedJets 2 B (iteratedFDeriv ℝ j f) :=
      (hhigh.of_le (by omega : 2+j ≤ r+2)).jet j
    have H := norm_fderiv_le_of_value_bound hh hA
      (fun y => hlow.bound j (by omega) y) ht x
    exact H.trans (add_le_add
      (div_le_div_of_nonneg_right (show 2*A ≤ 3*A by linarith) ht.le) le_rfl)

theorem eventually_small_of_values {J : Type}
    {s : Filter J} {I : Type} (f : J → I → X → Y) (r : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hhigh : ∀ᶠ n in s, ∀ i, QBoundedJets (r+1) B (f n i))
    (hvalue : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i x, ‖f n i x‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i, QBoundedJets r ε (f n i) := by
  induction r with
  | zero =>
    intro ε hε
    filter_upwards [hhigh,hvalue ε hε] with n hn hv i
    refine ⟨hε.le,(hn i).smooth.of_le (by norm_num),?_⟩
    intro j hj x
    have hj0 : j=0 := by omega
    subst j
    simpa only [norm_iteratedFDeriv_zero] using hv i x
  | succ r ih =>
    intro ε hε
    let t := ε/(2*(B+ε+1))
    have ht : 0 < t := by dsimp only [t]; positivity
    have ht1 : t ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 2*(B+ε+1))).mpr
      linarith
    let δ := ε*t/6
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    have hhigh' : ∀ᶠ n in s, ∀ i, QBoundedJets (r+1) B (f n i) := by
      filter_upwards [hhigh] with n hn i
      exact (hn i).of_le (by omega)
    have hsmall := ih hhigh' δ hδ
    filter_upwards [hhigh,hsmall] with n hn hs i
    apply ((hn i).interpolate_succ (hs i) ht ht1).mono
    have hBt : B*t ≤ ε/2 := by
      have hden : 0 < B+ε+1 := by positivity
      have H : B/(B+ε+1) ≤ 1 := (div_le_one hden).mpr (by linarith)
      calc
        _ = (ε/2)*(B/(B+ε+1)) := by dsimp only [t]; field_simp
        _ ≤ ε/2 := mul_le_of_le_one_right (by positivity) H
    have hδt : 3*δ/t = ε/2 := by dsimp only [δ]; field_simp; ring
    rw [hδt]
    linarith only [hBt]

end SpatialInterpolation

end SKBarriers2.QBoundedJets

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def spatialTaylorDefectCoarseCoefficient (n : ℕ) (B : ℝ) : ℝ :=
  spatialStepDifferenceCoefficient n B+(2 : ℝ)^(n+1)*B^2+B

theorem qBoundedJets_stepTaylorDefect_coarse (n : ℕ) {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n+3) B f) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets (n+1) (spatialTaylorDefectCoarseCoefficient n B*‖v‖^2)
      (stepTaylorDefect m v f) := by
  have hB := hf.nonneg
  have hm0 := hm.1
  have hstep := qBoundedJets_step_sub n hf hm v hv hsmall
  have hd := (hf.derivativeJets.of_le (by omega : n+1 ≤ n+2)).apply_const v
  have hp := hd.mul hd
  have hmhalf : |m/2| ≤ 1 := by rw [abs_of_nonneg (by positivity : 0 ≤ m/2)]; linarith only [hm.2]
  have hprod := (hp.const_smul (m/2)).mono (mul_le_of_le_one_left hp.nonneg hmhalf)
  have hdd : QBoundedJets (n+1) (B*‖v‖^2) (directionalJet v 2 f) := by
    exact qBoundedJets_iff_qBddSmooth.mpr (directionalJet_smooth (r := n+1) 1 hf v)
  have hh := (hdd.const_smul (1/2 : ℝ)).mono
    (mul_le_of_le_one_left hdd.nonneg (by norm_num))
  have H := hstep.sub (hprod.add hh)
  convert H using 1
  · unfold spatialTaylorDefectCoarseCoefficient
    ring
  · funext x
    simp only [stepTaylorDefect,smul_eq_mul]
    ring

theorem qBoundedJets_normalized_stepTaylorDefect (n : ℕ) {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n+3) B f) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets (n+1) (spatialTaylorDefectCoarseCoefficient n B)
      (fun x => (‖v‖^2)⁻¹*stepTaylorDefect m v f x) := by
  have H := (qBoundedJets_stepTaylorDefect_coarse n hf hm v hv hsmall).const_smul (‖v‖^2)⁻¹
  apply H.mono
  have hB := hf.nonneg
  have hK : 0 ≤ spatialTaylorDefectCoarseCoefficient n B := by
    have hS := spatialStepDifferenceCoefficient_nonneg n hf.nonneg
    dsimp only [spatialTaylorDefectCoarseCoefficient]
    positivity
  rw [abs_inv,abs_of_nonneg (sq_nonneg ‖v‖)]
  by_cases hv0 : ‖v‖^2=0
  · simp only [hv0,inv_zero,zero_mul,hK]
  · have hvnorm : ‖v‖ ≠ 0 := by intro H; exact hv0 (by rw [H]; norm_num)
    exact le_of_eq (by field_simp [hvnorm])

theorem abs_normalized_stepTaylorDefect_le {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) (x : E) :
    |(‖v‖^2)⁻¹*stepTaylorDefect m v f x| ≤ B*pathExpansionConstant B*‖v‖^2 := by
  have hvalue : |stepTaylorDefect m v f x| ≤ B*pathExpansionConstant B*‖v‖^4 := by
    have H := abs_step_generator_remainder_le hf le_rfl hm v x hv
    convert H using 1
    congr 1
    unfold stepTaylorDefect
    ring
  have hB := hf.nonneg
  have hP := pathExpansionConstant_nonneg hB
  rw [abs_mul,abs_inv,abs_of_nonneg (sq_nonneg ‖v‖)]
  by_cases hv0 : ‖v‖^2=0
  · simp [hv0]
  · calc
      _ ≤ (‖v‖^2)⁻¹*(B*pathExpansionConstant B*‖v‖^4) :=
        mul_le_mul_of_nonneg_left hvalue (inv_nonneg.mpr (sq_nonneg _))
      _ = _ := by field_simp

theorem eventually_small_normalized_stepTaylorDefect {J I : Type} {s : Filter J}
    (f : J → I → E → ℝ) (m : J → I → ℝ) (v : J → I → E) (r : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hf : ∀ᶠ n in s, ∀ i, QPotential (r+4) B (f n i))
    (hm : ∀ᶠ n in s, ∀ i, m n i ∈ Icc (0 : ℝ) 1)
    (hv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i, ‖v n i‖^2 ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i,
      QBoundedJets r ε (fun x => (‖v n i‖^2)⁻¹*stepTaylorDefect (m n i) (v n i) (f n i) x) := by
  let K := spatialTaylorDefectCoarseCoefficient r B
  have hK : 0 ≤ K := by
    have H := spatialStepDifferenceCoefficient_nonneg r hB
    dsimp only [K,spatialTaylorDefectCoarseCoefficient]
    positivity
  let η := min 1 (1/(2*B+1))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hsteps : ∀ᶠ n in s, ∀ i, ‖v n i‖ ≤ 1 ∧
      m n i*(B*‖v n i‖^2) ≤ 1/2 := by
    filter_upwards [hm,hv η hη] with n hn he i
    have he1 : ‖v n i‖^2 ≤ 1 := (he i).trans (min_le_left _ _)
    have hv1 : ‖v n i‖ ≤ 1 := by nlinarith only [he1,norm_nonneg (v n i)]
    have hshort : (2*B+1)*‖v n i‖^2 ≤ 1 := by
      have H := (le_div_iff₀ (by positivity : 0 < 2*B+1)).mp
        ((he i).trans (min_le_right _ _))
      nlinarith only [H]
    refine ⟨hv1,?_⟩
    have H := mul_le_of_le_one_left (mul_nonneg hB (sq_nonneg ‖v n i‖)) (hn i).2
    nlinarith only [H,hshort,sq_nonneg ‖v n i‖]
  have hhigh : ∀ᶠ n in s, ∀ i,
      QBoundedJets (r+1) K
        (fun x => (‖v n i‖^2)⁻¹*stepTaylorDefect (m n i) (v n i) (f n i) x) := by
    filter_upwards [hf,hm,hsteps] with n hfn hmn hs i
    exact qBoundedJets_normalized_stepTaylorDefect r ((hfn i).of_le (by omega))
      (hmn i) (v n i) (hs i).1 (hs i).2
  have hvalue : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i x,
      ‖(‖v n i‖^2)⁻¹*stepTaylorDefect (m n i) (v n i) (f n i) x‖ ≤ ε := by
    intro ε hε
    let C := B*pathExpansionConstant B
    have hC : 0 ≤ C := mul_nonneg hB (pathExpansionConstant_nonneg hB)
    filter_upwards [hf,hm,hsteps,hv (ε/(C+1)) (by positivity)] with n hfn hmn hs he i x
    have H := abs_normalized_stepTaylorDefect_le ((hfn i).of_le (by omega))
      (hmn i) (v n i) (hs i).1 x
    rw [Real.norm_eq_abs]
    calc
      _ ≤ C*‖v n i‖^2 := H
      _ ≤ C*(ε/(C+1)) := mul_le_mul_of_nonneg_left (he i) hC
      _ ≤ ε := by
        have HC : C/(C+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
        have H := mul_le_of_le_one_right hε.le HC
        convert H using 1; ring
  exact QBoundedJets.eventually_small_of_values _ r hK hhigh hvalue

theorem normalized_stepTaylorDefect_spatial_eventually {B M h : ℝ}
    (hB : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : E → ℝ, QPotential 8 B f →
      ∀ m : ℝ, m ∈ Icc (0 : ℝ) 1 → ∀ v : E, ‖v‖^2 ≤ M*h/(N:ℝ) →
      QBoundedJets 4 ε (fun x => (‖v‖^2)⁻¹*stepTaylorDefect m v f x) := by
  classical
  let I := {p : (E → ℝ) × ℝ × E // QPotential 8 B p.1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1}
  let F : ℕ → I → E → ℝ := fun _ i => i.val.1
  let m : ℕ → I → ℝ := fun _ i => i.val.2.1
  let v : ℕ → I → E := fun N i =>
    if ‖i.val.2.2‖^2 ≤ M*h/(N:ℝ) then i.val.2.2 else 0
  have hf : ∀ᶠ N : ℕ in atTop, ∀ i, QPotential 8 B (F N i) :=
    Eventually.of_forall (fun _ i => i.property.1)
  have hm : ∀ᶠ N : ℕ in atTop, ∀ i, m N i ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall (fun _ i => i.property.2)
  have hlim : Tendsto (fun N : ℕ => M*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hv : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ i, ‖v N i‖^2 ≤ δ := by
    intro δ hδ
    filter_upwards [hlim.eventually (eventually_le_nhds hδ)] with N hn i
    dsimp only [v]
    split_ifs with hi
    · exact hi.trans hn
    · simpa only [norm_zero,zero_pow (by norm_num : 2 ≠ 0)] using hδ.le
  have H := eventually_small_normalized_stepTaylorDefect F m v 4 hB hf hm hv ε hε
  filter_upwards [H] with N hn f hfn a ha w hw
  let i : I := ⟨(f,a,w),hfn,ha⟩
  have Hi := hn i
  simpa only [F,m,v,i,ite_eq_left hw] using Hi

theorem qBoundedJets_stepTaylorDefect_of_normalized {r : ℕ} {C m : ℝ}
    {f : E → ℝ} {v : E}
    (h : QBoundedJets r C (fun x => (‖v‖^2)⁻¹*stepTaylorDefect m v f x)) :
    QBoundedJets r (C*‖v‖^2) (stepTaylorDefect m v f) := by
  convert h.const_smul (‖v‖^2) using 1
  · rw [abs_of_nonneg (sq_nonneg ‖v‖)]
    ring
  · funext x
    by_cases hv : v=0
    · subst v
      simp [stepTaylorDefect,vectorStep_zero,directionalJet]
    · have hs : ‖v‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
      simp only [smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hs,one_mul]

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem movingAverage_window_direction_budget (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
        ‖(p k).2‖ ≤ L*Real.sqrt (h/(N:ℝ)) ∧
        ‖deriv (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N:ℝ)) ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ L*Real.sqrt (h/(N:ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (hbound β h hh N i k hk).2

theorem scalarData_window_secondMovingAverageSource {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ᶠ N : ℕ in atTop,
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      ∀ C A Q : ℝ, ∀ g a q : E → ℝ,
      QBoundedJets 2 C g → QBoundedJets 2 A a → QBoundedJets 0 Q q → ∀ x : E,
      let α := cdf (D.μ : Measure ℝ)
      let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
      let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
      let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
      |secondMovingAverageSource (p k).1 (deriv (fun t => (p t).1) k)
        (deriv (deriv (fun t => (p t).1)) k) (p k).2
        (deriv (fun t => (p t).2) k) (deriv (deriv (fun t => (p t).2)) k)
        F (G 1) (G 2) g a q x| ≤ Q+K*(C+A)*h/(N:ℝ) := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,_,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    obtain ⟨L,hL,hdir⟩ := movingAverage_window_direction_budget β
    let T := secondAverageTransportCoefficient (secondMovingAverageScale B R R)
      (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B) (defectNoiseMomentBound 3 B)
    have hT : 0 ≤ T := by
      dsimp only [T,secondAverageTransportCoefficient,secondMovingAverageScale,defectNoiseMomentBound]
      positivity
    refine ⟨T*L^2,min hV (min hJ (min hE 1)),min kapE (1/2),by positivity,
      lt_min hhV (lt_min hhJ (lt_min hhE (by norm_num))),lt_min hkapE (by norm_num),?_⟩
    intro r hr h hh hh0
    have hlim : Tendsto (fun N : ℕ => L^2*h/(N:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hsmall
    intro lam hlam j k hk C A Q g a q hg ha hq x
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
    let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
    have hhV' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhE' := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hkhalf := hk.trans (min_le_right _ _)
    have hp : p ∈ windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N :=
      orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    have hinputs := (hvar r hr h hh hhV' N hN lam hlam k hkhalf).2 p hp
    have hds := hdir _ _ _ hh.le N p hp k hkhalf
    obtain ⟨hG1,hG2⟩ := hjets r hr h hh hhJ' N hN lam hlam j k hkhalf
    have hRG : R*h ≤ R := mul_le_of_le_one_right hR.le hh1
    have hf₁ : QBoundedJets 1 R (G 1) := (hG1.of_le (by norm_num : 1 ≤ 6)).mono hRG
    have hf₂ : QBoundedJets 1 R (G 2) := (hG2.of_le (by norm_num : 1 ≤ 4)).mono hRG
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k (hk.trans (min_le_left _ _)) N hN
    obtain ⟨hinner,_⟩ := hEN lam hlam
    have hf : QPotential 3 B F := by
      simpa only [F,orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner j.val (by rw [windowMassPath_length]; exact j.isLt)).of_le (by norm_num : 3 ≤ 10)
    let d := L*Real.sqrt (h/(N:ℝ))
    have hd : 0 ≤ d := by dsimp only [d]; positivity
    have hsq : d^2 = L^2*h/(N:ℝ) := by
      dsimp only [d]
      rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
      ring
    have hd1 : d ≤ 1 := by nlinarith only [hd,hsq,hsmall]
    have H := abs_secondMovingAverageSource_le hf hf₁ hf₂ hg ha hq
      ⟨ha0.le.trans hinputs.2.1.1,hinputs.2.1.2⟩ hinputs.2.2.1 hinputs.2.2.2
      hd hd1 (p k).2 (deriv (fun t => (p t).2) k)
      (deriv (deriv (fun t => (p t).2)) k) hds.1 hds.2.1 hds.2.2 x
    exact H.trans_eq (by rw [hsq]; dsimp only [T]; ring)
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

theorem scalarData_window_stepTaylorDefect_spatial_c4 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ h0 kap : ℝ, 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N),
      ∀ k : ℝ, |k| ≤ kap →
      let α := cdf (D.μ : Measure ℝ)
      let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
      let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
      let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
      let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
      QBoundedJets 4 (ε*‖v‖^2) (stepTaylorDefect m v F) := by
  obtain ⟨B,a0,S,h0,kap,hB,ha0,_,hh0,hkap,hentropy⟩ :=
    scalarData_uniformWindowEntropyInputs D hl hu
  refine ⟨h0,kap,hh0,hkap,?_⟩
  intro r hr h hh hhh0 ε hε
  filter_upwards [normalized_stepTaylorDefect_spatial_eventually
      (M := S) (h := h) hB hε,eventually_ge_atTop (1 : ℕ)] with N hn hN
  intro lam hlam j k hk
  dsimp only
  let α := cdf (D.μ : Measure ℝ)
  let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
  let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
  let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
  let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
  obtain ⟨_,hEN⟩ := hentropy r hr h hh hhh0 k hk N hN
  obtain ⟨hinner,hentry⟩ := hEN lam hlam
  have hf : QPotential 8 B F := by
    simpa only [F,orderedInnerChain,massPath,List.map_drop,windowEntryIndex,jj] using
      (hinner jj.val jj.isLt).of_le (by norm_num : 8 ≤ 10)
  have hm : m ∈ Icc (0 : ℝ) 1 := ⟨ha0.le.trans (hentry jj).1.1,(hentry jj).1.2⟩
  have hv : ‖v‖^2 ≤ S*h/(N:ℝ) := (hentry jj).2
  exact qBoundedJets_stepTaylorDefect_of_normalized (hn F hf m hm v hv)

end SKBarriers2.Corner

namespace SKBarriers2.ParamChain

local notation "E" => (Fin 3 → ℝ)

section MovingTestIdentification

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : NormedAddCommGroup (P × E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × E →L[ℝ] ℝ) := inferInstance

private theorem test_spatial_slice_jets {G : P × E → ℝ} (hG : ContDiff ℝ 2 G)
    (q u : P) (y w : E) :
    fderiv ℝ (fun z => G (q,z)) y w = fderiv ℝ G (q,y) (0,w) ∧
    fderiv ℝ (fderiv ℝ (fun z => G (q,z))) y w w =
      fderiv ℝ (fderiv ℝ G) (q,y) (0,w) (0,w) ∧
    fderiv ℝ (fun z => fderiv ℝ G (q,z) (u,0)) y w =
      fderiv ℝ (fderiv ℝ G) (q,y) (0,w) (u,0) := by
  let L : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  have heq (z : E) : L z+(q,0) = (q,z) := by ext <;> simp [L]
  have h1 := first_affine_apply hG L (q,0) y w
  have h2 := second_affine_apply hG L (q,0) y w w
  simp_rw [heq] at h1 h2
  have hp : HasFDerivAt (fun z : E => (q,z)) L y :=
    (hasFDerivAt_const q y).prodMk (hasFDerivAt_id y)
  have hd := (((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (q,y)).hasFDerivAt.comp y hp).clm_apply (hasFDerivAt_const (u,(0 : E)) y)
  have h3 := congrArg (fun D : E →L[ℝ] ℝ => D w) hd.fderiv
  change fderiv ℝ (fun z => fderiv ℝ G (q,z) (u,0)) y w =
    fderiv ℝ G (q,y) 0+fderiv ℝ (fderiv ℝ G) (q,y) (0,w) (u,0) at h3
  exact ⟨h1,h2,by simpa only [map_zero,zero_add] using h3⟩

private theorem test_mixed_parameter_spatial {G : P × E → ℝ} (hG : ContDiff ℝ 2 G)
    (q u : P) (y w : E) (t : ℝ) :
    fderiv ℝ (fderiv ℝ G) (q,y) (u,t • w) (u,t • w) =
      fderiv ℝ (fderiv ℝ G) (q,y) (u,0) (u,0)+
        2*t*fderiv ℝ (fun z => fderiv ℝ G (q,z) (u,0)) y w+
        t^2*fderiv ℝ (fderiv ℝ (fun z => G (q,z))) y w w := by
  have hsplit : (u,t • w) = (u,(0 : E))+t • ((0 : P),w) := by ext <;> simp
  have hs := (hG.contDiffAt.isSymmSndFDerivAt (by norm_num) :
    IsSymmSndFDerivAt ℝ G (q,y)) (u,0) (0,w)
  obtain ⟨_,h2,h3⟩ := test_spatial_slice_jets hG q u y w
  rw [hsplit]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [hs,← h2,← h3]
  ring

private theorem test_second_curve {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {G : Y → ℝ} (hG : ContDiff ℝ 2 G) {p : ℝ → Y} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) :
    deriv (deriv (fun t => G (p t))) k =
      fderiv ℝ (fderiv ℝ G) (p k) (deriv p k) (deriv p k)+
        fderiv ℝ G (p k) (deriv (deriv p) k) := by
  have hd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have heq : deriv (fun t => G (p t)) =ᶠ[𝓝 k] fun t => fderiv ℝ G (p t) (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact ((hG.differentiable (by norm_num) (p t)).hasFDerivAt.comp_hasDerivAt t
      (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hD := ((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (p k)).hasFDerivAt.comp_hasDerivAt k hd
  rw [heq.deriv_eq]
  exact (hD.clm_apply hdd).deriv

theorem movingInput_curve_testJets {G : P × E → ℝ} (hG : ContDiff ℝ 2 G)
    (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (x : E) (t : ℝ) :
    let g := fun y => G (p k,y)
    let a := fun y => fderiv ℝ G (p k,y) (deriv p k,0)
    let q := fun y => fderiv ℝ (fderiv ℝ G) (p k,y) (deriv p k,0) (deriv p k,0)+
      fderiv ℝ G (p k,y) (deriv (deriv p) k,0)
    deriv (fun r => G (p r,x+t • V (p r))) k =
        StepCalculus.movingAverageTestFirst (V (p k)) (V (deriv p k)) g a x t ∧
      deriv (deriv (fun r => G (p r,x+t • V (p r)))) k =
        StepCalculus.movingAverageTestSecond (V (p k)) (V (deriv p k))
          (V (deriv (deriv p) k)) g a q x t := by
  dsimp only
  let c : ℝ → P × E := fun r => (p r,x+t • V (p r))
  have hc : ContDiffAt ℝ 2 c k := hp.prodMk
    (contDiffAt_const.add ((V.contDiff.contDiffAt.comp k hp).const_smul t))
  have hcd (r : ℝ) (hr : DifferentiableAt ℝ p r) :
      HasDerivAt c (deriv p r,t • V (deriv p r)) r := by
    exact hr.hasDerivAt.prodMk
      (((V.hasFDerivAt.comp_hasDerivAt r hr.hasDerivAt).const_smul t).const_add x)
  have hc1 : deriv c k = (deriv p k,t • V (deriv p k)) :=
    (hcd k (hp.differentiableAt (by norm_num))).deriv
  have hceq : deriv c =ᶠ[𝓝 k] fun r => (deriv p r,t • V (deriv p r)) := by
    filter_upwards [hp.eventually (by norm_num)] with r hr
    exact (hcd r (hr.differentiableAt (by norm_num))).deriv
  have hc2 : deriv (deriv c) k = (deriv (deriv p) k,t • V (deriv (deriv p) k)) := by
    rw [hceq.deriv_eq]
    have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
    exact (hdd.prodMk ((V.hasFDerivAt.comp_hasDerivAt k hdd).const_smul t)).deriv
  have hsplit (u : P) : fderiv ℝ G (p k,x+t • V (p k)) (u,t • V u) =
      fderiv ℝ G (p k,x+t • V (p k)) (u,0)+
        t*fderiv ℝ (fun z => G (p k,z)) (x+t • V (p k)) (V u) := by
    have he : (u,t • V u) = (u,(0 : E))+t • ((0 : P),V u) := by ext <;> simp
    rw [he,map_add,map_smul,← (test_spatial_slice_jets hG (p k) u
      (x+t • V (p k)) (V u)).1]
    rfl
  constructor
  · have H := ((hG.differentiable (by norm_num) (c k)).hasFDerivAt.comp_hasDerivAt k
      (hcd k (hp.differentiableAt (by norm_num)))).deriv
    change deriv (fun r => G (p r,x+t • V (p r))) k = _ at H
    rw [H,hsplit]
    rfl
  · have H := test_second_curve hG hc
    change deriv (deriv (fun r => G (p r,x+t • V (p r)))) k = _ at H
    rw [hc1,hc2] at H
    rw [H,test_mixed_parameter_spatial hG (p k) (deriv p k)
      (x+t • V (p k)) (V (deriv p k)) t,hsplit]
    unfold StepCalculus.movingAverageTestSecond
    ring

end MovingTestIdentification

end SKBarriers2.ParamChain

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

section ActualSecondAverage

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem second_deriv_exponential_movingAverage {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : E) :
    let f := fun y => F (p k,y)
    let f₁ := fun y => fderiv ℝ F (p k,y) (deriv p k,0)
    let f₂ := fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0)+
      fderiv ℝ F (p k,y) (deriv (deriv p) k,0)
    let g := fun y => G (p k,y)
    let a := fun y => fderiv ℝ G (p k,y) (deriv p k,0)
    let q := fun y => fderiv ℝ (fderiv ℝ G) (p k,y) (deriv p k,0) (deriv p k,0)+
      fderiv ℝ G (p k,y) (deriv (deriv p) k,0)
    let m := Real.exp (M (p k))
    let dm := m*M (deriv p k)
    let ddm := m*((M (deriv p k))^2+M (deriv (deriv p) k))
    ContDiffAt ℝ 2 (fun r => tiltedAverage (Real.exp (M (p r))) (V (p r))
        (fun y => F (p r,y)) (fun y => G (p r,y)) x) k ∧
      deriv (deriv (fun r => tiltedAverage (Real.exp (M (p r))) (V (p r))
        (fun y => F (p r,y)) (fun y => G (p r,y)) x)) k =
        secondMovingAverageSource m dm ddm (V (p k)) (V (deriv p k))
          (V (deriv (deriv p) k)) f f₁ f₂ g a q x := by
  dsimp only
  let I := ParamChain.movingLogInput F M V
  let J : P × (E × ℝ) → ℝ := fun z => G (z.1,z.2.1+z.2.2 • V z.1)
  let H : P × (E × ℝ) → ℝ := fun z => I z-I (z.1,(z.2.1,0))
  have hI : ParamRegular I := ParamChain.regular_movingLogInput hF M V
  have hJ : ParamSmooth J := ParamChain.smooth_movingInput hG V
  let L : E × ℝ →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).prod (0 : E × ℝ →L[ℝ] ℝ)
  have hH : ParamRegular H := by
    convert hI.add ((hI.fieldComp L).const_mul (-1)) using 1
    funext z
    change I z-I (z.1,(z.2.1,0)) = I z+(-1)*I (z.1,(z.2.1,0))
    ring
  have hlaw (r : P) : gaussianStepLaw 1
      (fun z : (P × E) × ℝ => H (z.1.1,(z.1.2,z.2))) (r,x) =
      stepLaw (Real.exp (M r)) (V r) (fun y => F (r,y)) x := by
    have HT := tilted_tilted (μ := gaussianReal 0 1)
      (f := fun _ : ℝ => -I (r,(x,0))) (integrable_const _) (fun t => I (r,(x,t)))
    rw [tilted_const] at HT
    unfold gaussianStepLaw
    simp only [one_mul]
    calc
      _ = (gaussianReal 0 1).tilted
          ((fun _ : ℝ => -I (r,(x,0)))+(fun t => I (r,(x,t)))) := by
        congr 1
        funext t
        simp only [H,Pi.add_apply]
        ring
      _ = (gaussianReal 0 1).tilted (fun t => I (r,(x,t))) := HT.symm
      _ = _ := rfl
  have heq : (fun r => OAI.SK.Analytic.gaussianAverage 1
      (fun z : (P × E) × ℝ => H (z.1.1,(z.1.2,z.2)))
      (fun z : (P × E) × ℝ => J (z.1.1,(z.1.2,z.2))) (p r,x)) =
      fun r => tiltedAverage (Real.exp (M (p r))) (V (p r))
        (fun y => F (p r,y)) (fun y => G (p r,y)) x := by
    funext r
    unfold OAI.SK.Analytic.gaussianAverage
    rw [hlaw]
    rfl
  have hIc (t : ℝ) : ContDiffAt ℝ 2 (fun r => I (p r,(x,t))) k :=
    hI.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)
  have hIfirst (t : ℝ) : deriv (fun r => I (p r,(x,t))) k =
      fderiv ℝ I (p k,(x,t)) (deriv p k,0) := by
    simpa only [Function.comp_def] using
      ((hI.1.differentiable (by norm_num) (p k,(x,t))).hasFDerivAt.comp_hasDerivAt k
        ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k (x,t)))).deriv
  have hfirst (t : ℝ) : deriv (fun r => H (p r,(x,t))) k =
      firstAverageScore (Real.exp (M (p k)))
        (Real.exp (M (p k))*M (deriv p k)) (V (p k)) (V (deriv p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0)) x t := by
    change deriv (fun r => I (p r,(x,t))-I (p r,(x,0))) k = _
    rw [deriv_fun_sub ((hIc t).differentiableAt (by norm_num))
      ((hIc 0).differentiableAt (by norm_num)),hIfirst,hIfirst]
    exact (movingLogInput_centered_scores hF M V (p k) (deriv p k)
      (deriv (deriv p) k) x t).1
  have hsecond (t : ℝ) : deriv (deriv (fun r => H (p r,(x,t)))) k =
      secondAverageScoreLinear (Real.exp (M (p k)))
        (Real.exp (M (p k))*M (deriv p k))
        (Real.exp (M (p k))*((M (deriv p k))^2+M (deriv (deriv p) k)))
        (V (p k)) (V (deriv p k)) (V (deriv (deriv p) k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0)+
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0)) x t+
      secondAverageScoreQuadratic (Real.exp (M (p k))) (V (p k)) (V (deriv p k))
        (fun y => F (p k,y)) x t := by
    have HD := iteratedDeriv_fun_sub (hIc t) (hIc 0)
    simp only [iteratedDeriv_succ,iteratedDeriv_zero] at HD
    change deriv (deriv (fun r => I (p r,(x,t))-I (p r,(x,0)))) k = _
    rw [HD,ParamChain.second_parameter_curve hI.1 hp (x,t),
      ParamChain.second_parameter_curve hI.1 hp (x,0)]
    exact (movingLogInput_centered_scores hF M V (p k) (deriv p k)
      (deriv (deriv p) k) x t).2
  have hnorm := ParamChain.gaussianAverage_curve_second_covariance hH hJ hp x
  dsimp only at hnorm
  rw [heq,hlaw] at hnorm
  simp_rw [hfirst,hsecond] at hnorm
  have htestfirst (t : ℝ) := (ParamChain.movingInput_curve_testJets hG.1 V hp x t).1
  have htestsecond (t : ℝ) := (ParamChain.movingInput_curve_testJets hG.1 V hp x t).2
  change (∀ t, deriv (fun r => J (p r,(x,t))) k = _) at htestfirst
  change (∀ t, deriv (deriv (fun r => J (p r,(x,t)))) k = _) at htestsecond
  simp_rw [htestfirst,htestsecond] at hnorm
  exact hnorm

end ActualSecondAverage

end SKBarriers2.StepCalculus
