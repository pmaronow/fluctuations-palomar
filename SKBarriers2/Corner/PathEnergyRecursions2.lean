module

public import SKBarriers2.Corner.PathEnergyRecursions

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

private theorem zero_test_jets (n : ℕ) : QBoundedJets n 0 (fun _ : E => (0:ℝ)) := by
  refine ⟨le_rfl,contDiff_const,?_⟩
  intro j hj x
  simp

theorem secondMovingAverageSource_split_top {B C D Q : ℝ} {f g a q : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 C g)
    (ha : QBoundedJets 2 D a) (hq : QBoundedJets 0 Q q)
    (m dm ddm : ℝ) (v w b : E) (f₁ f₂ : E → ℝ) (x : E) :
    secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x =
      tiltedAverage m v f q x+
        secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a (fun _ => 0) x := by
  have hqI := integrable_tilted_shift hf (by norm_num) hq m v x
  have haI := (integrable_noise_test_powers hf (ha.derivativeJets.apply_const w) m v x).1
  have hgI := (integrable_noise_test_powers hf
    ((hg.derivativeJets.of_le (by norm_num : 1 ≤ 2)).apply_const b) m v x).1
  have hhI := (integrable_noise_test_powers hf
    ((hg.derivativeJets.derivativeJets.apply_const w).apply_const w) m v x).2
  have hremI : Integrable (fun t =>
      2*(t*fderiv ℝ a (x+t • v) w)+
        t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w+
        t*fderiv ℝ g (x+t • v) b) (stepLaw m v f x) :=
    ((haI.const_mul 2).add hhI).add hgI
  have hsplit :
      noiseMean m v f x (movingAverageTestSecond v w b g a q x) =
        tiltedAverage m v f q x+
          noiseMean m v f x (movingAverageTestSecond v w b g a (fun _ => 0) x) := by
    unfold noiseMean tiltedAverage movingAverageTestSecond
    have he (t : ℝ) :
        q (x+t • v)+2*(t*fderiv ℝ a (x+t • v) w)+
          t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w+t*fderiv ℝ g (x+t • v) b =
        q (x+t • v)+(2*(t*fderiv ℝ a (x+t • v) w)+
          t^2*fderiv ℝ (fderiv ℝ g) (x+t • v) w w+t*fderiv ℝ g (x+t • v) b) := by ring
    simp_rw [he]
    rw [integral_add hqI hremI]
    simp only [zero_add]
  unfold secondMovingAverageSource secondAverageTransport
  dsimp only [noiseMean] at hsplit
  rw [hsplit]
  ring

theorem abs_secondMovingAverageSource_sub_energy {B A H C D Q e m dm ddm : ℝ}
    {f f₁ f₂ g a q : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 1 A f₁) (hf₂ : QBoundedJets 1 H f₂)
    (hg : QBoundedJets 3 C g) (ha : QBoundedJets 2 D a) (hq : QBoundedJets 2 Q q)
    (hm : m ∈ Icc (0:ℝ) 1) (hdm : |dm| ≤ 1) (hddm : |ddm| ≤ 1)
    (v w b : E) (he : ‖v‖^2+‖w‖^2+‖b‖^2 ≤ e) (he1 : e ≤ 1) (x : E) :
    |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a q x-q x| ≤
      ((1+B)^2*Q+secondAverageTransportCoefficient (secondMovingAverageScale B A H)
        (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B)
        (defectNoiseMomentBound 3 B)*(C+D))*e := by
  have hvE : ‖v‖^2 ≤ e := by nlinarith only [he,sq_nonneg ‖w‖,sq_nonneg ‖b‖]
  have hv : ‖v‖ ≤ 1 := by nlinarith only [hvE,he1,norm_nonneg v]
  have hweak := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hq).potential (by norm_num) hm v x hv
  have hsource := abs_secondMovingAverageSource_energy hf hf₁ hf₂
    (hg.of_le (by norm_num : 2 ≤ 3)) ha (zero_test_jets 0) hm hdm hddm v w b he he1 x
  rw [secondMovingAverageSource_split_top hf hg ha (hq.of_le (by norm_num))]
  calc
    _ = |(tiltedAverage m v f q x-q x)+
        secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a (fun _ => 0) x| := by congr 1; ring
    _ ≤ |tiltedAverage m v f q x-q x|+
        |secondMovingAverageSource m dm ddm v w b f f₁ f₂ g a (fun _ => 0) x| := abs_add_le _ _
    _ ≤ Q*(1+B)^2*‖v‖^2+
        (0+secondAverageTransportCoefficient (secondMovingAverageScale B A H)
          (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B)
          (defectNoiseMomentBound 3 B)*(C+D)*e) := add_le_add hweak hsource
    _ ≤ _ := by
      have H' := mul_le_mul_of_nonneg_left hvE
        (show 0 ≤ Q*(1+B)^2 by positivity [hq.nonneg])
      nlinarith only [H']

theorem qBoundedJets_firstTiltedAverageSource_sub {B A C D : ℝ}
    {f F g a : E → ℝ} (hf : QPotential 5 B f) (hF : QBoundedJets 3 A F)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 D a)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (dm : ℝ) (v w : E)
    (hv : ‖v‖ ≤ 1) (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets 2
      (D*tiltedDifferenceCoefficient 2 B*‖v‖^2+
        firstTiltedAverageSourceBound B A C 0 m dm v w)
      (fun x => firstTiltedAverageSource m v f F g a dm w x-a x) := by
  have hweak := qBoundedJets_tiltedAverage_sub 2 hf (by norm_num) (by norm_num) ha hm v hv hsmall
  have hsource := qBoundedJets_firstTiltedAverageSource hf hF hg (zero_test_jets 2)
    hm dm v w hv hsmall
  have he : (fun x => firstTiltedAverageSource m v f F g a dm w x-a x) =
      fun x => (tiltedAverage m v f a x-a x)+
        firstTiltedAverageSource m v f F g (fun _ => 0) dm w x := by
    funext x
    simp only [firstTiltedAverageSource,tiltedAverage,integral_zero]
    ring
  rw [he]
  exact hweak.add hsource

theorem qBoundedJets_firstTiltedAverageSource_sub_energy {B A C D R e : ℝ}
    {f F g a : E → ℝ} (hf : QPotential 5 B f) (hF : QBoundedJets 3 A F)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 D a)
    (hR : 0 ≤ R) (hAR : A ≤ R) {m dm : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (hdm : |dm| ≤ 1) (v w : E) (hv : ‖v‖ ≤ 1)
    (hsmall : m*(B*‖v‖^2) ≤ 1/2) (he : ‖v‖^2+‖w‖^2 ≤ e) :
    QBoundedJets 2
      ((D*tiltedDifferenceCoefficient 2 B+firstTiltedTransportCoefficient B R*C)*e)
      (fun x => firstTiltedAverageSource m v f F g a dm w x-a x) := by
  apply (qBoundedJets_firstTiltedAverageSource_sub hf hF hg ha hm dm v w hv hsmall).mono
  have H := firstTiltedAverageSourceBound_le (B := B) hF.nonneg hg.nonneg (le_refl (0:ℝ))
    hR hAR hm hdm v w hv
  have hfirst : firstTiltedAverageSourceBound B A C 0 m dm v w ≤
      firstTiltedTransportCoefficient B R*C*e := by
    have H' : firstTiltedAverageSourceBound B A C 0 m dm v w ≤
        firstTiltedTransportCoefficient B R*C*(‖v‖^2+‖w‖^2) := by
      simpa only [mul_zero,zero_add] using H
    have hT : 0 ≤ firstTiltedTransportCoefficient B R := by
      unfold firstTiltedTransportCoefficient
      positivity
    exact H'.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hT hg.nonneg))
  have hvE : ‖v‖^2 ≤ e := by nlinarith only [he,sq_nonneg ‖w‖]
  have hweak := mul_le_mul_of_nonneg_left hvE
    (mul_nonneg ha.nonneg (tiltedDifferenceCoefficient_nonneg 2 B))
  nlinarith only [hweak,hfirst]

def firstMovingAverageQuadratic (m dm : ℝ) (v w : E)
    (f f₁ g a : E → ℝ) (x : E) : ℝ :=
  a x+pathGenerator m v f a x+mixedDirectionSource m v w f g x+
    fderiv ℝ g x v*(dm*fderiv ℝ f x v+
      m*(fderiv ℝ f₁ x v+fderiv ℝ f x w))

theorem covariance_shift_eq_spatialCovariance {B C D : ℝ} {f g a : E → ℝ}
    (hf : QPotential 3 B f) (hg : QPotential 3 C g) (ha : QPotential 3 D a)
    (m : ℝ) (v x : E) :
    covariance (fun t => g (x+t • v)) (fun t => a (x+t • v)) (stepLaw m v f x) =
      spatialCovariance m v f g a x := by
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hl (b : E → ℝ) {R : ℝ} (hb : QPotential 3 R b) :
      MemLp (fun t => b (x+t • v)) 2 (stepLaw m v f x) := by
    apply memLp_noise_of_growth hf m v x
    · exact hb.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    · obtain ⟨J,M,hJ,hM,H⟩ := (hb.boundedDerivs (by norm_num)).hasExpGrowth
      refine ⟨J*Real.exp (M*‖x‖),M*‖v‖,by positivity,by positivity,?_⟩
      intro t
      calc
        _ ≤ J*Real.exp (M*‖x+t • v‖) := H (x+t • v)
        _ ≤ J*Real.exp (M*(‖x‖+‖t • v‖)) := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by
          simp only [norm_smul,Real.norm_eq_abs]
          rw [show M*(‖x‖+|t| *‖v‖) = M*‖x‖+(M*‖v‖)*|t| by ring,Real.exp_add]
          ring
  rw [covariance_eq_sub (hl g hg) (hl a ha)]
  rfl

def firstWeakDefectCoefficient (B A C D m dm : ℝ) : ℝ :=
  D*pathExpansionConstant B+
    C*(|dm| *B*potentialCovarianceDefectCoefficient B+
      |m| *A*(18*pathExpansionConstant B+(1+B)^4)+
      (1+4*B)*(1+B)^2+2*|m| *(B+4*B^2)+4*|m| *B*(1+B)^2)

set_option maxHeartbeats 800000 in
theorem abs_firstMovingAverageSource_sub_quadratic_le {B A C D m dm d : ℝ}
    {f f₁ g a : E → ℝ} (hf : QPotential 5 B f) (hf₁ : QBoundedJets 4 A f₁)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 D a)
    (hm : m ∈ Icc (0:ℝ) 1) (hd : 0 ≤ d) (v w x : E)
    (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hv1 : ‖v‖ ≤ 1)
    (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    |firstTiltedAverageSource m v f f₁ g a dm w x-
        firstMovingAverageQuadratic m dm v w f f₁ g a x| ≤
      firstWeakDefectCoefficient B A C D m dm*d^4 := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have hC := hg.nonneg
  have hD := ha.nonneg
  have hP := pathExpansionConstant_nonneg hB
  have hV := potentialCovarianceDefectCoefficient_nonneg hB
  have hfa := abs_noiseMean_generator_remainder_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp ha).potential (by norm_num) hm v x hv1
  have hmix : QBoundedJets 2 ((1+4*B)*C*‖v‖*‖w‖) (mixedDirectionSource m v w f g) := by
    simpa only [show (2:ℝ)^2=4 by norm_num] using
      qBoundedJets_mixedDirectionSource_order (n := 1) (hf.of_le (by norm_num : 4 ≤ 5)) hg hm v w
  have hmixBias := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hmix).potential (by norm_num) hm v x hv1
  have hmass := abs_potentialCovariance_sub_gradient_le (hf.of_le (by norm_num : 3 ≤ 5))
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 3 ≤ 4))).potential
    (hf.of_le (by norm_num : 3 ≤ 5)) hm v x hv1
  have hterm := abs_spatialCovariance_sub_gradient_le hf (by norm_num) hg hf₁ hm v x hv1
  have hdir := qBoundedJets_directionSource (hf.of_le (by norm_num : 4 ≤ 5)) hm v w
  have hcovDir := (qBoundedJets_spatialCovariance 0 hf (by norm_num) (by norm_num)
    (hg.of_le (by norm_num : 1 ≤ 4)) (hdir.of_le (by norm_num : 1 ≤ 2)) hm v hsmall).norm_le x
  have hprod := (hg.derivativeJets.of_le (by norm_num : 2 ≤ 3) |>.apply_const v).mul
    (hf.derivativeJets.of_le (by norm_num : 2 ≤ 4) |>.apply_const w)
  have hprodBias := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hprod).potential (by norm_num) hm v x hv1
  have he : firstTiltedAverageSource m v f f₁ g a dm w x-
      firstMovingAverageQuadratic m dm v w f f₁ g a x =
      (tiltedAverage m v f a x-a x-m*fderiv ℝ f x v*fderiv ℝ a x v-directionalJet v 2 a x/2)+
      (tiltedAverage m v f (mixedDirectionSource m v w f g) x-mixedDirectionSource m v w f g x)+
      dm*(spatialCovariance m v f g f x-fderiv ℝ g x v*fderiv ℝ f x v)+
      m*(spatialCovariance m v f g f₁ x-fderiv ℝ g x v*fderiv ℝ f₁ x v)+
      m*spatialCovariance m v f g (directionSource m v w f) x+
      m*(tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x-
        fderiv ℝ g x v*fderiv ℝ f x w) := by
    unfold firstTiltedAverageSource firstMovingAverageQuadratic pathGenerator
    rw [covariance_shift_eq_spatialCovariance (hf.of_le (by norm_num : 3 ≤ 5))
      (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 3 ≤ 4))).potential
      (hf.of_le (by norm_num : 3 ≤ 5))]
    ring
  have htri (a b c d e f : ℝ) : |a+b+c+d+e+f| ≤ |a|+|b|+|c|+|d|+|e|+|f| := by
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)
  rw [he]
  simp only [Real.norm_eq_abs,covarianceJetCoefficient] at hcovDir
  norm_num only [show (2:ℝ)^2=4 by norm_num] at hcovDir hprodBias
  apply (htri _ _ _ _ _ _).trans
  simp only [abs_mul]
  calc
    _ ≤ D*pathExpansionConstant B*‖v‖^4+
        ((1+4*B)*C*‖v‖*‖w‖)*(1+B)^2*‖v‖^2+
        |dm| *(C*B*potentialCovarianceDefectCoefficient B*‖v‖^4)+
        |m| *(C*A*(18*pathExpansionConstant B+(1+B)^4)*‖v‖^4)+
        |m| *(2*C*((B+4*B^2)*‖v‖*‖w‖)*‖v‖^2)+
        |m| *((4*(C*‖v‖)*(B*‖w‖))*(1+B)^2*‖v‖^2) := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hfa hmixBias)
        (mul_le_mul_of_nonneg_left hmass (abs_nonneg dm)))
        (mul_le_mul_of_nonneg_left hterm (abs_nonneg m)))
        (mul_le_mul_of_nonneg_left hcovDir (abs_nonneg m)))
        (mul_le_mul_of_nonneg_left hprodBias (abs_nonneg m))
    _ ≤ D*pathExpansionConstant B*d^4+
        ((1+4*B)*C*d*d)*(1+B)^2*d^2+
        |dm| *(C*B*potentialCovarianceDefectCoefficient B*d^4)+
        |m| *(C*A*(18*pathExpansionConstant B+(1+B)^4)*d^4)+
        |m| *(2*C*((B+4*B^2)*d*d)*d^2)+
        |m| *((4*(C*d)*(B*d))*(1+B)^2*d^2) := by gcongr
    _ = _ := by unfold firstWeakDefectCoefficient; ring

def firstWeakSpatialCoefficient (B A C D m dm : ℝ) : ℝ :=
  D*tiltedDifferenceCoefficient 3 B+
    |tiltedCoarseCoefficient 3 B| *(1+8*B)*C+
    |dm| *|potentialCovarianceCoefficient 3 B| *C*B+
    |m| *|covarianceJetCoefficient 3 B| *C*A+
    |m| *|covarianceJetCoefficient 3 B| *C*(B+16*B^2)+
    |m| *|tiltedCoarseCoefficient 3 B| *8*C*B+
    (8*B+1)*D+(1+8*B)*C+8*C*(|dm| *B+|m| *(A+B))

set_option maxHeartbeats 1000000 in
theorem qBoundedJets_firstWeakDefect_coarse {B A C D m dm d : ℝ}
    {f f₁ g a : E → ℝ} (hf : QPotential 6 B f) (hf₁ : QBoundedJets 4 A f₁)
    (hg : QBoundedJets 5 C g) (ha : QBoundedJets 5 D a)
    (hm : m ∈ Icc (0:ℝ) 1) (hd : 0 ≤ d) (v w : E)
    (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (hv1 : ‖v‖ ≤ 1)
    (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets 3 (firstWeakSpatialCoefficient B A C D m dm*d^2)
      (fun x => firstTiltedAverageSource m v f f₁ g a dm w x-
        firstMovingAverageQuadratic m dm v w f f₁ g a x) := by
  have hB := hf.nonneg
  have hA := hf₁.nonneg
  have hC := hg.nonneg
  have hD := ha.nonneg
  have hweak := qBoundedJets_tiltedAverage_sub 3 hf (by norm_num) (by norm_num) ha hm v hv1 hsmall
  have hmix := qBoundedJets_mixedDirectionSource_order (n := 2)
    (hf.of_le (by norm_num : 5 ≤ 6)) hg hm v w
  have hmixAvg := qBoundedJets_tiltedAverage_coarse 3 hf (by norm_num) (by norm_num) hmix hm v
  have hmass := (qBoundedJets_potentialCovariance (n := 3)
    (hf.of_le (by norm_num : 5 ≤ 6))
    (qBoundedJets_iff_qBddSmooth.mp hg).potential
    (hf.of_le (by norm_num : 5 ≤ 6)) hm v hv1).const_smul dm
  have hmass' : QBoundedJets 3
      (|dm| *(potentialCovarianceCoefficient 3 B*C*B*‖v‖^2))
      (fun x => dm*spatialCovariance m v f g f x) := by
    have he : (fun x => dm*spatialCovariance m v f g f x) = fun x =>
        dm*covariance (fun t => g (x+t • v)) (fun t => f (x+t • v)) (stepLaw m v f x) := by
      funext x
      rw [covariance_shift_eq_spatialCovariance (hf.of_le (by norm_num : 3 ≤ 6))
        (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 3 ≤ 5))).potential
        (hf.of_le (by norm_num : 3 ≤ 6))]
    rw [he]
    exact hmass
  have hterm := (qBoundedJets_spatialCovariance 3 hf (by norm_num) (by norm_num)
    (hg.of_le (by norm_num : 4 ≤ 5)) hf₁ hm v hsmall).const_smul m
  have hdir := qBoundedJets_directionSource hf hm v w
  have hcovDir := (qBoundedJets_spatialCovariance 3 hf (by norm_num) (by norm_num)
    (hg.of_le (by norm_num : 4 ≤ 5)) hdir hm v hsmall).const_smul m
  have hdg := (hg.derivativeJets.of_le (by norm_num : 3 ≤ 4)).apply_const v
  have hdf := (hf.derivativeJets.of_le (by norm_num : 3 ≤ 5)).apply_const v
  have hdfw := (hf.derivativeJets.of_le (by norm_num : 3 ≤ 5)).apply_const w
  have hdf₁ := hf₁.derivativeJets.apply_const v
  have hprod := hdg.mul hdfw
  have hprodAvg := (qBoundedJets_tiltedAverage_coarse 3 hf (by norm_num) (by norm_num)
    hprod hm v).const_smul m
  have hgen := qBoundedJets_pathGenerator_order (hf.of_le (by norm_num : 4 ≤ 6)) ha hm v
  have hquadratic := (hgen.add hmix).add
    (hdg.mul ((hdf.const_smul dm).add ((hdf₁.add hdfw).const_smul m)))
  have H := ((((hweak.add hmixAvg).add hmass').add hterm).add hcovDir).add hprodAvg
  have H' := H.sub hquadratic
  have he : (fun x =>
      tiltedAverage m v f a x-a x+tiltedAverage m v f (mixedDirectionSource m v w f g) x+
        dm*spatialCovariance m v f g f x+m*spatialCovariance m v f g f₁ x+
        m*spatialCovariance m v f g (directionSource m v w f) x+
        m*tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x-
      ((pathGenerator m v f a x+mixedDirectionSource m v w f g x)+
        fderiv ℝ g x v*(dm*fderiv ℝ f x v+
          m*(fderiv ℝ f₁ x v+fderiv ℝ f x w)))) =
      fun x => firstTiltedAverageSource m v f f₁ g a dm w x-
        firstMovingAverageQuadratic m dm v w f f₁ g a x := by
    funext x
    unfold firstTiltedAverageSource firstMovingAverageQuadratic
    rw [covariance_shift_eq_spatialCovariance (hf.of_le (by norm_num : 3 ≤ 6))
      (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 3 ≤ 5))).potential
      (hf.of_le (by norm_num : 3 ≤ 6))]
    ring
  change QBoundedJets 3 _ (fun x =>
      tiltedAverage m v f a x-a x+tiltedAverage m v f (mixedDirectionSource m v w f g) x+
        dm*spatialCovariance m v f g f x+m*spatialCovariance m v f g f₁ x+
        m*spatialCovariance m v f g (directionSource m v w f) x+
        m*tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ f y w) x-
      ((pathGenerator m v f a x+mixedDirectionSource m v w f g x)+
        fderiv ℝ g x v*(dm*fderiv ℝ f x v+
          m*(fderiv ℝ f₁ x v+fderiv ℝ f x w)))) at H'
  rw [he] at H'
  apply H'.mono
  have hv2 : ‖v‖^2 ≤ 1 := by nlinarith only [hv1,norm_nonneg v]
  norm_num only [show (2:ℝ)^3=8 by norm_num,show (2:ℝ)^4=16 by norm_num]
  have ht0 := tiltedDifferenceCoefficient_nonneg 3 B
  calc
    _ ≤ D*tiltedDifferenceCoefficient 3 B*d^2+
        |tiltedCoarseCoefficient 3 B| *((1+8*B)*C*d*d)+
        |dm| *(|potentialCovarianceCoefficient 3 B| *C*B*d^2)+
        |m| *(|covarianceJetCoefficient 3 B| *C*A*d^2)+
        |m| *(|covarianceJetCoefficient 3 B| *C*((B+16*B^2)*d*d)*1)+
        |m| *(|tiltedCoarseCoefficient 3 B| *(8*(C*d)*(B*d)))+
        (((8*B+1)*D*d^2+(1+8*B)*C*d*d)+
          8*(C*d)*(|dm| *(B*d)+|m| *(A*d+B*d))) := by
      gcongr <;> exact le_abs_self _
    _ = _ := by unfold firstWeakSpatialCoefficient; ring

theorem eventually_small_firstWeakDefect {J I : Type} {s : Filter J}
    (f f₁ g a : J → I → E → ℝ) (m dm : J → I → ℝ) (v w : J → I → E)
    (d : J → ℝ) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : ∀ᶠ n in s, ∀ i, QPotential 6 B (f n i))
    (hf₁ : ∀ᶠ n in s, ∀ i, QBoundedJets 4 R (f₁ n i))
    (hg : ∀ᶠ n in s, ∀ i, QBoundedJets 5 R (g n i))
    (ha : ∀ᶠ n in s, ∀ i, QBoundedJets 5 R (a n i))
    (hm : ∀ᶠ n in s, ∀ i, m n i ∈ Icc (0:ℝ) 1)
    (hdm : ∀ᶠ n in s, ∀ i, |dm n i| ≤ 1)
    (hd : ∀ᶠ n in s, 0 < d n)
    (hvw : ∀ᶠ n in s, ∀ i, ‖v n i‖ ≤ d n ∧ ‖w n i‖ ≤ d n)
    (hlim : Tendsto (fun n => d n^2) s (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i,
      QBoundedJets 2 (ε*d n^2)
        (fun x => firstTiltedAverageSource (m n i) (v n i) (f n i) (f₁ n i)
          (g n i) (a n i) (dm n i) (w n i) x-
          firstMovingAverageQuadratic (m n i) (dm n i) (v n i) (w n i)
            (f n i) (f₁ n i) (g n i) (a n i) x) := by
  let K := firstWeakSpatialCoefficient B R R R 1 1
  let V := firstWeakDefectCoefficient B R R R 1 1
  have hT := tiltedDifferenceCoefficient_nonneg 3 B
  have hP := pathExpansionConstant_nonneg hB
  have hQ := potentialCovarianceDefectCoefficient_nonneg hB
  have hK : 0 ≤ K := by dsimp only [K,firstWeakSpatialCoefficient]; positivity
  have hV : 0 ≤ V := by dsimp only [V,firstWeakDefectCoefficient]; positivity
  let F : J → I → E → ℝ := fun n i x => (d n^2)⁻¹*
    (firstTiltedAverageSource (m n i) (v n i) (f n i) (f₁ n i)
      (g n i) (a n i) (dm n i) (w n i) x-
      firstMovingAverageQuadratic (m n i) (dm n i) (v n i) (w n i)
        (f n i) (f₁ n i) (g n i) (a n i) x)
  have hsteps : ∀ᶠ n in s, ∀ i, ‖v n i‖ ≤ 1 ∧
      m n i*(B*‖v n i‖^2) ≤ 1/2 := by
    filter_upwards [hm,hvw,hlim.eventually (eventually_le_nhds
      (lt_min (by norm_num : (0:ℝ) < 1) (by positivity : 0 < 1/(2*B+1))))] with n hmn hn hs i
    have hs1 := hs.trans (min_le_left _ _)
    have hv2 := pow_le_pow_left₀ (norm_nonneg _) (hn i).1 2
    have hv1 : ‖v n i‖ ≤ 1 := by nlinarith only [hv2,hs1,norm_nonneg (v n i)]
    have H := (le_div_iff₀ (by positivity : 0 < 2*B+1)).mp (hs.trans (min_le_right _ _))
    have H' := mul_le_of_le_one_left (mul_nonneg hB (sq_nonneg ‖v n i‖)) (hmn i).2
    refine ⟨hv1,?_⟩
    have H'' := mul_le_mul_of_nonneg_left hv2 hB
    nlinarith only [H,H',H'',sq_nonneg (d n)]
  have hcoef {m dm : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (hdm : |dm| ≤ 1) :
      firstWeakSpatialCoefficient B R R R m dm ≤ K ∧
      firstWeakDefectCoefficient B R R R m dm ≤ V := by
    have hmabs : |m| ≤ 1 := by rw [abs_of_nonneg hm.1]; exact hm.2
    constructor
    · dsimp only [K,firstWeakSpatialCoefficient]
      norm_num only [abs_one]
      gcongr
    · dsimp only [V,firstWeakDefectCoefficient]
      norm_num only [abs_one]
      gcongr <;> linarith only [hmabs]
  have hhigh : ∀ᶠ n in s, ∀ i, QBoundedJets 3 K (F n i) := by
    filter_upwards [hf,hf₁,hg,ha,hm,hdm,hd,hvw,hsteps] with n hfn hf₁n hgn han hmn hdmn hdn hn hs i
    have H := (qBoundedJets_firstWeakDefect_coarse (hfn i) (hf₁n i) (hgn i) (han i)
      (hmn i) hdn.le (v n i) (w n i) (hn i).1 (hn i).2 (hs i).1 (hs i).2).mono
      (mul_le_mul_of_nonneg_right (hcoef (hmn i) (hdmn i)).1 (sq_nonneg (d n)))
    have H' := H.const_smul (d n^2)⁻¹
    apply H'.mono
    rw [abs_inv,abs_of_nonneg (sq_nonneg (d n))]
    have hd0 := hdn.ne'
    exact le_of_eq (by field_simp)
  have hvalue : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in s, ∀ i x, ‖F n i x‖ ≤ ε := by
    intro ε hε
    filter_upwards [hf,hf₁,hg,ha,hm,hdm,hd,hvw,hsteps,
      hlim.eventually (eventually_le_nhds (by positivity : 0 < ε/(V+1)))] with
      n hfn hf₁n hgn han hmn hdmn hdn hn hs hsmall i x
    have H := (abs_firstMovingAverageSource_sub_quadratic_le
      ((hfn i).of_le (by norm_num : 5 ≤ 6)) (hf₁n i)
      ((hgn i).of_le (by norm_num : 4 ≤ 5)) ((han i).of_le (by norm_num : 4 ≤ 5))
      (hmn i) hdn.le (v n i) (w n i) x (hn i).1 (hn i).2 (hs i).1 (hs i).2).trans
      (mul_le_mul_of_nonneg_right (hcoef (hmn i) (hdmn i)).2 (pow_nonneg hdn.le 4))
    have hd0 := hdn.ne'
    rw [Real.norm_eq_abs]
    calc
      _ = (d n^2)⁻¹*|firstTiltedAverageSource (m n i) (v n i) (f n i) (f₁ n i)
          (g n i) (a n i) (dm n i) (w n i) x-
          firstMovingAverageQuadratic (m n i) (dm n i) (v n i) (w n i)
            (f n i) (f₁ n i) (g n i) (a n i) x| := by
        dsimp only [F]
        rw [abs_mul,abs_inv,abs_of_nonneg (sq_nonneg (d n))]
      _ ≤ (d n^2)⁻¹*(V*d n^4) := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (sq_nonneg _))
      _ = V*d n^2 := by field_simp
      _ ≤ V*(ε/(V+1)) := mul_le_mul_of_nonneg_left hsmall hV
      _ ≤ ε := by
        convert mul_le_of_le_one_right hε.le
          ((div_le_one (by positivity : 0 < V+1)).mpr (by linarith : V ≤ V+1)) using 1
        ring
  intro ε hε
  filter_upwards [QBoundedJets.eventually_small_of_values F 2 hK hhigh hvalue ε hε,hd] with n hn hdn i
  have H := (hn i).const_smul (d n^2)
  have hd0 : d n^2 ≠ 0 := pow_ne_zero 2 hdn.ne'
  convert H using 1
  · rw [abs_of_nonneg (sq_nonneg (d n))]; ring
  · funext x
    dsimp only [F]
    simp only [smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hd0,one_mul]

end SKBarriers2.StepCalculus

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem qBoundedJets_chain_sub_order (n : ℕ) {B : ℝ} {f : E → ℝ}
    (ps : List (ℝ × E)) (hjets : SpatialChainJets (n+3) B ps f)
    (hm : ∀ p ∈ ps, p.1 ∈ Icc (0:ℝ) 1)
    (hv : ∀ p ∈ ps, ‖p.2‖ ≤ 1 ∧ p.1*(B*‖p.2‖^2) ≤ 1/2) :
    QBoundedJets (n+1) (spatialStepDifferenceCoefficient n B*chainEnergy ps)
      (fun x => vectorIncrementChain ps f x-f x) := by
  induction ps with
  | nil =>
    refine ⟨by simp [chainEnergy],((hjets 0).smooth.sub (hjets 0).smooth).of_le
      (by exact_mod_cast (show n+1 ≤ n+3 by omega)),?_⟩
    intro j hj x
    have he : (fun x => vectorIncrementChain [] f x-f x) = fun _ => (0:ℝ) := by funext x; exact sub_self _
    rw [he]
    simp [chainEnergy]
  | cons p ps ih =>
    have ht : SpatialChainJets (n+3) B ps f := fun i => by
      simpa only [List.drop_succ_cons] using hjets (i+1)
    have hhead := qBoundedJets_step_sub n (ht 0) (hm p (by simp)) p.2
      (hv p (by simp)).1 (hv p (by simp)).2
    have htail := ih ht (fun q hq => hm q (by simp [hq])) (fun q hq => hv q (by simp [hq]))
    have he : (fun x => vectorIncrementChain (p::ps) f x-f x) =
        fun x => (vectorStep p.1 p.2 (vectorIncrementChain ps f) x-vectorIncrementChain ps f x)+
          (vectorIncrementChain ps f x-f x) := by funext x; dsimp only [vectorIncrementChain]; ring
    rw [he,chainEnergy_cons]
    simpa only [List.drop_zero,mul_add] using hhead.add htail

theorem qBoundedJets_gradientSquare_sub_order (n : ℕ) {B H : ℝ} {f F : E → ℝ}
    (hf : QPotential (n+1) B f) (hF : QPotential (n+1) B F)
    (hdiff : QBoundedJets (n+1) H (fun x => F x-f x)) (w : E) :
    QBoundedJets n ((2:ℝ)^n*H*(2*B)*‖w‖^2)
      (fun x => (fderiv ℝ F x w)^2-(fderiv ℝ f x w)^2) := by
  have hd := hdiff.derivativeJets.apply_const w
  have hs := (hF.derivativeJets.apply_const w).add (hf.derivativeJets.apply_const w)
  have he : (fun x => fderiv ℝ (fun y => F y-f y) x w) =
      fun x => fderiv ℝ F x w-fderiv ℝ f x w := by
    funext x
    rw [fderiv_fun_sub (hF.smooth.differentiable (by simp) x)
      (hf.smooth.differentiable (by simp) x),sub_apply]
  rw [he] at hd
  convert hd.mul hs using 1
  · ring
  · funext x; ring

theorem abs_potential_noise_linear_remainder {B : ℝ} {f : E → ℝ}
    (hf : QPotential 2 B f) (v x : E) (t : ℝ) :
    |f (x+t • v)-f x-t*fderiv ℝ f x v| ≤ B*‖v‖^2*|t|^2 := by
  have H := hf.taylor_linear_remainder_le le_rfl x (t • v)
  convert H using 1
  · rw [map_smul,smul_eq_mul]
  · rw [norm_smul,Real.norm_eq_abs,mul_pow]
    ring

theorem abs_noisy_gradient_sub_local {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) (v w x : E) (t : ℝ) :
    |t*(fderiv ℝ f (x+t • v) w-fderiv ℝ f x w)| ≤ B*‖v‖*‖w‖*|t|^2 := by
  have hd := (hf.derivativeJets.apply_const w).lipschitzWith
  have H := hd.norm_sub_le (x+t • v) x
  change ‖fderiv ℝ f (x+t • v) w-fderiv ℝ f x w‖ ≤ (B*‖w‖)*‖x+t • v-x‖ at H
  rw [Real.norm_eq_abs,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at H
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left H (abs_nonneg t)).trans_eq (by ring)

theorem abs_firstAverageScore_sub_tangent {B A m dm d : ℝ} {f f₁ : E → ℝ}
    (hf : QPotential 3 B f) (hf₁ : QBoundedJets 2 A f₁) (hd : 0 ≤ d)
    (v w x : E) (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) (t : ℝ) :
    |firstAverageScore m dm v w f f₁ x t-
      t*(dm*fderiv ℝ f x v+m*(fderiv ℝ f₁ x v+fderiv ℝ f x w))| ≤
      (|dm| *B+|m| *(A+B))*d^2*|t|^2 := by
  have hF := abs_potential_noise_linear_remainder (hf.of_le (by norm_num : 2 ≤ 3)) v x t
  have hG := abs_potential_noise_linear_remainder
    (qBoundedJets_iff_qBddSmooth.mp hf₁).potential v x t
  have hD := abs_noisy_gradient_sub_local hf v w x t
  have he : firstAverageScore m dm v w f f₁ x t-
      t*(dm*fderiv ℝ f x v+m*(fderiv ℝ f₁ x v+fderiv ℝ f x w)) =
      dm*(f (x+t • v)-f x-t*fderiv ℝ f x v)+
        m*((f₁ (x+t • v)-f₁ x-t*fderiv ℝ f₁ x v)+
          t*(fderiv ℝ f (x+t • v) w-fderiv ℝ f x w)) := by
    unfold firstAverageScore
    ring
  rw [he]
  calc
    _ ≤ |dm| *|f (x+t • v)-f x-t*fderiv ℝ f x v|+
        |m| *(|f₁ (x+t • v)-f₁ x-t*fderiv ℝ f₁ x v|+
          |t*(fderiv ℝ f (x+t • v) w-fderiv ℝ f x w)|) := by
      exact (abs_add_le _ _).trans (by rw [abs_mul,abs_mul]; gcongr; exact abs_add_le _ _)
    _ ≤ |dm| *(B*‖v‖^2*|t|^2)+|m| *(A*‖v‖^2*|t|^2+B*‖v‖*‖w‖*|t|^2) := by
      gcongr
    _ ≤ |dm| *(B*d^2*|t|^2)+|m| *(A*d^2*|t|^2+B*d*d*|t|^2) := by
      have hB := hf.nonneg
      have hA := hf₁.nonneg
      gcongr
    _ = _ := by ring

private theorem weak_growth_line {g : E → ℝ} (hg : HasExpGrowth g) (x v : E) :
    HasExpGrowth (fun t : ℝ => g (x+t • v)) := by
  obtain ⟨C,M,hC,hM,H⟩ := hg
  refine ⟨C*Real.exp (M*‖x‖),M*‖v‖,by positivity,by positivity,?_⟩
  intro t
  calc
    _ ≤ C*Real.exp (M*‖x+t • v‖) := H _
    _ ≤ C*Real.exp (M*(‖x‖+‖t • v‖)) := by gcongr; exact norm_add_le _ _
    _ = _ := by
      simp only [norm_smul,Real.norm_eq_abs]
      rw [show M*(‖x‖+|t| *‖v‖) = M*‖x‖+(M*‖v‖)*|t| by ring,Real.exp_add]
      ring

set_option maxHeartbeats 800000 in
theorem covariance_noisy_test_eq {B C D : ℝ} {f g a : E → ℝ}
    (hf : QPotential 4 B f) (hg : QPotential 3 C g) (ha : QBoundedJets 4 D a)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v w x : E) :
    covariance (fun t => g (x+t • v)) (fun t => t*fderiv ℝ a (x+t • v) w)
        (stepLaw m v f x) =
      spatialCovariance m v f g (mixedDirectionSource m v w f a) x+
        tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ a y w) x := by
  have hf3 := hf.of_le (by norm_num : 3 ≤ 4)
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  let P : ℝ → ℝ := fun t => g (x+t • v)*fderiv ℝ a (x+t • v) w
  let Q : ℝ → ℝ := fun t => fderiv ℝ g (x+t • v) v*fderiv ℝ a (x+t • v) w+
    g (x+t • v)*fderiv ℝ (fderiv ℝ a) (x+t • v) v w
  have hW := (ha.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w
  have hV := (hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const v
  have hH := ((ha.derivativeJets.derivativeJets.of_le (by norm_num : 2 ≤ 2)).apply_const v).apply_const w
  have hG := hg.derivativeJets.apply_const v
  have hJ := qBoundedJets_mixedDirectionSource_order (n := 1) hf ha hm v w
  have hline : Continuous (fun t : ℝ => x+t • v) := continuous_const.add (continuous_id.smul continuous_const)
  have hlineD (t : ℝ) : HasDerivAt (fun r : ℝ => x+r • v) v t := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
  have hdW (t : ℝ) : HasDerivAt (fun r => fderiv ℝ a (x+r • v) w)
      (fderiv ℝ (fderiv ℝ a) (x+t • v) v w) t := by
    have H := (((ha.smooth.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (x+t • v)).hasFDerivAt.comp_hasDerivAt t (hlineD t)).clm_apply (hasDerivAt_const t w)
    simpa only [Function.comp_def,map_zero,add_zero] using H
  have hdG (t : ℝ) : HasDerivAt (fun r => g (x+r • v)) (fderiv ℝ g (x+t • v) v) t :=
    (hg.smooth.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hlineD t)
  have hd (t : ℝ) : HasDerivAt P (Q t) t := (hdG t).mul (hdW t)
  have hgg := weak_growth_line (hg.boundedDerivs (by norm_num)).hasExpGrowth x v
  have hgW : HasExpGrowth (fun t : ℝ => fderiv ℝ a (x+t • v) w) :=
    HasExpGrowth.of_bounded hW.nonneg (fun t => hW.norm_le (x+t • v))
  have hgH : HasExpGrowth (fun t : ℝ => fderiv ℝ (fderiv ℝ a) (x+t • v) v w) :=
    HasExpGrowth.of_bounded hH.nonneg (fun t => hH.norm_le (x+t • v))
  have hgG : HasExpGrowth (fun t : ℝ => fderiv ℝ g (x+t • v) v) :=
    HasExpGrowth.of_bounded hG.nonneg (fun t => hG.norm_le (x+t • v))
  have hcQ : Continuous Q := ((hG.smooth.continuous.comp hline).mul
    (hW.smooth.continuous.comp hline)).add
    ((hg.smooth.continuous.comp hline).mul (hH.smooth.continuous.comp hline))
  have H := tilted_integration_by_parts hf (by norm_num) m v x hd hcQ (hgg.mul hgW)
    ((hgG.mul hgW).add (hgg.mul hgH))
  have hgm : MemLp (fun t : ℝ => g (x+t • v)) 2 μ :=
    memLp_noise_of_growth hf3 m v x (hg.smooth.continuous.comp hline) hgg
  have hbounded {n : ℕ} {A : ℝ} {b : E → ℝ} (hb : QBoundedJets n A b) :
      MemLp (fun t => b (x+t • v)) 2 μ :=
    MemLp.of_bound (hb.smooth.continuous.comp hline).aestronglyMeasurable A
      (ae_of_all _ (fun t => hb.norm_le _))
  have hJm := hbounded hJ
  have hHm := hbounded hH
  have hGWm := hbounded (hG.mul hW)
  have hWVm := hbounded (hW.mul hV)
  have hiQ : Integrable Q μ := (hGWm.integrable (by norm_num)).add (hgm.integrable_mul hHm)
  have hiProd : Integrable (fun t : ℝ => g (x+t • v)*
      (fderiv ℝ a (x+t • v) w*fderiv ℝ f (x+t • v) v)) μ := hgm.integrable_mul hWVm
  have hiGJ : Integrable (fun t : ℝ => g (x+t • v)*mixedDirectionSource m v w f a (x+t • v)) μ :=
    hgm.integrable_mul hJm
  have hpoint (t : ℝ) : Q t+m*(P t*fderiv ℝ f (x+t • v) v) =
      fderiv ℝ g (x+t • v) v*fderiv ℝ a (x+t • v) w+
        g (x+t • v)*mixedDirectionSource m v w f a (x+t • v) := by
    dsimp only [P,Q,mixedDirectionSource]
    ring
  have hcombine : noiseMean m v f x Q+
      m*noiseMean m v f x (fun t => P t*fderiv ℝ f (x+t • v) v) =
      tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ a y w) x+
        tiltedAverage m v f (fun y => g y*mixedDirectionSource m v w f a y) x := by
    unfold noiseMean tiltedAverage
    rw [← integral_const_mul,← integral_add hiQ (by
      convert hiProd.const_mul m using 1
      funext t; dsimp only [P]; ring)]
    simp_rw [hpoint]
    rw [integral_add (hGWm.integrable (by norm_num)) hiGJ]
  rw [hcombine] at H
  have hNm : MemLp (fun t => t*fderiv ℝ a (x+t • v) w) 2 μ :=
    memLp_noise_of_growth hf3 m v x (continuous_id.mul (hW.smooth.continuous.comp hline))
      ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).mul hgW)
  rw [covariance_eq_sub hgm hNm]
  simp only [Pi.mul_apply]
  have hprod : (∫ t, g (x+t • v)*(t*fderiv ℝ a (x+t • v) w) ∂μ) =
      noiseMean m v f x (fun t => t*P t) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by dsimp only [P]; ring)
  rw [hprod,H]
  change _-tiltedAverage m v f g x*
    noiseMean m v f x (fun t => t*fderiv ℝ a (x+t • v) w) = _
  rw [noise_mixedDirectionSource_c2 (hf.of_le (by norm_num : 2 ≤ 4))
    (ha.of_le (by norm_num : 2 ≤ 4))]
  unfold spatialCovariance
  ring

def noisyTestCovarianceDefectCoefficient (B : ℝ) : ℝ :=
  |potentialCovarianceCoefficient 0 B| *(1+4*B)+4*(1+B)^2

theorem abs_covariance_noisy_test_sub_gradient_le {B C D : ℝ} {f g a : E → ℝ}
    (hf : QPotential 4 B f) (hg : QPotential 3 C g) (ha : QBoundedJets 4 D a)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v w x : E) (hv : ‖v‖ ≤ 1) :
    |covariance (fun t => g (x+t • v)) (fun t => t*fderiv ℝ a (x+t • v) w)
        (stepLaw m v f x)-fderiv ℝ g x v*fderiv ℝ a x w| ≤
      C*D*noisyTestCovarianceDefectCoefficient B*‖v‖^3*‖w‖ := by
  have hJ : QBoundedJets 2 ((1+4*B)*D*‖v‖*‖w‖) (mixedDirectionSource m v w f a) := by
    simpa only [show (2:ℝ)^2=4 by norm_num] using
      qBoundedJets_mixedDirectionSource_order (n := 1) hf ha hm v w
  have hCov := abs_potential_bounded_covariance_le (hf.of_le (by norm_num : 3 ≤ 4)) hg hJ hm v x hv
  have hprod := (hg.derivativeJets.apply_const v).mul
    ((ha.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w)
  have hweak := abs_noiseMean_sub_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hprod).potential (by norm_num) hm v x hv
  rw [covariance_noisy_test_eq hf hg ha hm]
  have he : spatialCovariance m v f g (mixedDirectionSource m v w f a) x+
      tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ a y w) x-
        fderiv ℝ g x v*fderiv ℝ a x w =
      spatialCovariance m v f g (mixedDirectionSource m v w f a) x+
        (tiltedAverage m v f (fun y => fderiv ℝ g y v*fderiv ℝ a y w) x-
          fderiv ℝ g x v*fderiv ℝ a x w) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hCov hweak).trans_eq (by
    unfold noisyTestCovarianceDefectCoefficient
    norm_num
    ring))

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)
local notation "Curve" => (ℝ → ℝ × E)

def prefixEnergyEnvelope (e : Curve → ℝ) (K B : ℝ) : List Curve → ℝ × ℝ × ℝ
  | [] => (0,0,0)
  | p::tail =>
    let a := (prefixEnergyEnvelope e K B tail).1
    let b := (prefixEnergyEnvelope e K B tail).2.1
    let c := (prefixEnergyEnvelope e K B tail).2.2
    ((1+K*e p)*a+B*e p,
      (1+K*e p)*b+K*e p*a+B*e p,
      (1+K*e p)*c+K*e p*(a+b)+B*e p)

theorem prefixEnergy_envelopes_of_steps (qs : List Curve) (R : List Curve → ℝ → E → ℝ)
    (e : Curve → ℝ) (K B k : ℝ)
    (hzero : ∀ t x, R [] t x = 0)
    (hregular : ∀ front tail, qs = front++tail → ∀ x,
      ContDiffAt ℝ 2 (fun t => R tail t x) k)
    (hstep : ∀ front p tail, qs = front++p::tail → ∀ a b c : ℝ,
      QBoundedJets 4 a (R tail k) →
      QBoundedJets 2 b (fun x => deriv (fun t => R tail t x) k) →
      QBoundedJets 0 c (fun x => deriv (deriv (fun t => R tail t x)) k) →
      QBoundedJets 4 ((1+K*e p)*a+B*e p) (R (p::tail) k) ∧
      QBoundedJets 2 ((1+K*e p)*b+K*e p*a+B*e p)
        (fun x => deriv (fun t => R (p::tail) t x) k) ∧
      QBoundedJets 0 ((1+K*e p)*c+K*e p*(a+b)+B*e p)
        (fun x => deriv (deriv (fun t => R (p::tail) t x)) k)) :
    ∃ a b c : List Curve → ℝ,
      a [] ≤ 0 ∧ b [] ≤ 0 ∧ c [] ≤ 0 ∧
      (∀ front tail, qs = front++tail →
        (∀ x, ContDiffAt ℝ 2 (fun t => R tail t x) k) ∧
        QBoundedJets 4 (a tail) (R tail k) ∧
        QBoundedJets 2 (b tail) (fun x => deriv (fun t => R tail t x) k) ∧
        QBoundedJets 0 (c tail) (fun x => deriv (deriv (fun t => R tail t x)) k)) ∧
      (∀ front p tail, qs = front++p::tail → a (p::tail) ≤ (1+K*e p)*a tail+B*e p) ∧
      (∀ front p tail, qs = front++p::tail → b (p::tail) ≤ (1+K*e p)*b tail+K*e p*a tail+B*e p) ∧
      (∀ front p tail, qs = front++p::tail → c (p::tail) ≤ (1+K*e p)*c tail+K*e p*(a tail+b tail)+B*e p) := by
  let a := fun tail => (prefixEnergyEnvelope e K B tail).1
  let b := fun tail => (prefixEnergyEnvelope e K B tail).2.1
  let c := fun tail => (prefixEnergyEnvelope e K B tail).2.2
  have hz : R [] = fun _ _ => (0:ℝ) := funext (fun t => funext (fun x => hzero t x))
  have hjets (tail : List Curve) : ∀ front, qs = front++tail →
      QBoundedJets 4 (a tail) (R tail k) ∧
      QBoundedJets 2 (b tail) (fun x => deriv (fun t => R tail t x) k) ∧
      QBoundedJets 0 (c tail) (fun x => deriv (deriv (fun t => R tail t x)) k) := by
    induction tail with
    | nil =>
      intro front hfront
      refine ⟨?_,?_,?_⟩
      · simpa only [a,prefixEnergyEnvelope,hz] using (StepCalculus.zero_test_jets 4)
      · simpa only [b,prefixEnergyEnvelope,hz,deriv_const'] using (StepCalculus.zero_test_jets 2)
      · simpa only [c,prefixEnergyEnvelope,hz,deriv_const'] using (StepCalculus.zero_test_jets 0)
    | cons p tail ih =>
      intro front hfront
      have htail : qs = (front++[p])++tail := by simpa only [List.append_assoc,List.singleton_append] using hfront
      obtain ⟨ha,hb,hc⟩ := ih (front++[p]) htail
      exact hstep front p tail hfront (a tail) (b tail) (c tail) ha hb hc
  refine ⟨a,b,c,le_rfl,le_rfl,le_rfl,?_,?_,?_,?_⟩
  · intro front tail hfront
    exact ⟨hregular front tail hfront,hjets tail front hfront⟩
  · intro front p tail hfront
    exact le_rfl
  · intro front p tail hfront
    exact le_rfl
  · intro front p tail hfront
    exact le_rfl

theorem scalarData_window_weakBias_sources {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      ∀ C A Q : ℝ, ∀ g a q : E → ℝ,
      QBoundedJets 6 C g → QBoundedJets 4 A a → QBoundedJets 2 Q q →
      let α := cdf (D.μ : Measure ℝ)
      let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
      let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
      let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
      let dm := deriv (fun t => (p t).1) k
      let ddm := deriv (deriv (fun t => (p t).1)) k
      let w := deriv (fun t => (p t).2) k
      let b := deriv (deriv (fun t => (p t).2)) k
      let e := windowVariationEnergy k p
      QBoundedJets 4 (K*C*e) (fun x => tiltedAverage (p k).1 (p k).2 F g x-g x) ∧
        QBoundedJets 2 (K*(C+A)*e)
          (fun x => firstTiltedAverageSource (p k).1 (p k).2 F (G 1) g a dm w x-a x) ∧
        ∀ x : E, |secondMovingAverageSource (p k).1 dm ddm (p k).2 w b
          F (G 1) (G 2) g a q x-q x| ≤ K*(C+A+Q)*e := by
  by_cases hlu : l ≤ u
  · obtain ⟨V,a0,hV,hV0,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨R,hJ,hR,hhJ,hjets⟩ := scalarData_orderedInnerVariations_c6_c4 D hl hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    let T₁ := firstTiltedTransportCoefficient B R
    let T₂ := secondAverageTransportCoefficient (secondMovingAverageScale B R R)
      (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B) (defectNoiseMomentBound 3 B)
    let K := tiltedDifferenceCoefficient 4 B+tiltedDifferenceCoefficient 2 B+T₁+T₂+(1+B)^2
    have hT₁ : 0 ≤ T₁ := by dsimp only [T₁,firstTiltedTransportCoefficient]; positivity
    have hT₂ : 0 ≤ T₂ := by
      dsimp only [T₂,secondAverageTransportCoefficient,secondMovingAverageScale,defectNoiseMomentBound]
      positivity
    have hD₄ := tiltedDifferenceCoefficient_nonneg 4 B
    have hD₂ := tiltedDifferenceCoefficient_nonneg 2 B
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hD₄K : tiltedDifferenceCoefficient 4 B ≤ K := by dsimp only [K]; linarith [sq_nonneg (1+B)]
    have hD₂K : tiltedDifferenceCoefficient 2 B ≤ K := by dsimp only [K]; linarith [sq_nonneg (1+B)]
    have hT₁K : T₁ ≤ K := by dsimp only [K]; linarith [sq_nonneg (1+B)]
    have hT₂K : T₂ ≤ K := by dsimp only [K]; linarith [sq_nonneg (1+B)]
    have hBK : (1+B)^2 ≤ K := by dsimp only [K]; linarith
    let Z := V*(2*B+1)+1
    have hZ : 0 < Z := by dsimp only [Z]; positivity
    refine ⟨K,min hV (min hJ (min hE (min 1 (1/Z)))),min kapE (1/2),hK,
      lt_min hhV (lt_min hhJ (lt_min hhE (lt_min (by norm_num) (by positivity)))),
      lt_min hkapE (by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk C A Q g a q hg ha hq
    dsimp only
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let p := orderedWindowCurve β α (α (r-h)) (r-h) h N lam j
    let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
    let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
    let e := windowVariationEnergy k p
    have hhV' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhE' := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hh1 := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
    have hhZ := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
    have hp : p ∈ ps := orderedWindowCurve_mem β α (α (r-h)) (r-h) h N lam j
    obtain ⟨henergy,hinputs⟩ := hvar r hr h hh hhV' N hN lam hlam k (hk.trans (min_le_right _ _))
    have hentry := hinputs p hp
    have he0 : 0 ≤ e := windowVariationEnergy_nonneg k p
    have he : e ≤ V*h := by
      apply le_trans _ henergy
      exact List.single_le_sum (fun t ht => by
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp ht
        exact windowVariationEnergy_nonneg k p) _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    have hshort : Z*h ≤ 1 := by
      have H := (le_div_iff₀ hZ).mp hhZ
      nlinarith only [H]
    have he1 : e ≤ 1 := by
      have H'' := mul_le_mul_of_nonneg_right
        (show V ≤ Z by dsimp only [Z]; nlinarith [mul_nonneg hV0.le hB]) hh.le
      linarith only [he,hshort,H'']
    have hv2 : ‖(p k).2‖^2 ≤ e := by
      dsimp only [e,windowVariationEnergy]
      nlinarith only [sq_nonneg ‖deriv (fun t => (p t).2) k‖,
        sq_nonneg ‖deriv (deriv (fun t => (p t).2)) k‖]
    have hv : ‖(p k).2‖ ≤ 1 := by nlinarith only [hv2,he1,norm_nonneg ((p k).2)]
    have hcurv : (p k).1*(B*‖(p k).2‖^2) ≤ 1/2 := by
      have H := mul_le_mul_of_nonneg_left (hv2.trans he) hB
      have H' := mul_le_of_le_one_left (mul_nonneg hB (sq_nonneg ‖(p k).2‖)) hentry.2.1.2
      have H'' : 0 ≤ h := hh.le
      dsimp only [Z] at hshort
      nlinarith only [H,H',hshort,H'',mul_nonneg hV0.le hh.le]
    obtain ⟨hG₁,hG₂⟩ := hjets r hr h hh hhJ' N hN lam hlam j k (hk.trans (min_le_right _ _))
    have hRG : R*h ≤ R := mul_le_of_le_one_right hR.le hh1
    have hf₁ : QBoundedJets 3 R (G 1) := (hG₁.of_le (by norm_num : 3 ≤ 6)).mono hRG
    have hf₂ : QBoundedJets 1 R (G 2) := (hG₂.of_le (by norm_num : 1 ≤ 4)).mono hRG
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k (hk.trans (min_le_left _ _)) N hN
    obtain ⟨hinner,_⟩ := hEN lam hlam
    have hf : QPotential 6 B F := by
      simpa only [F,orderedInnerChain,massPath,List.map_drop,windowEntryIndex] using
        (hinner j.val (by rw [windowMassPath_length]; exact j.isLt)).of_le (by norm_num : 6 ≤ 10)
    have hm : (p k).1 ∈ Icc (0:ℝ) 1 := ⟨ha0.le.trans hentry.2.1.1,hentry.2.1.2⟩
    have hg0 := hg.nonneg
    have ha0' := ha.nonneg
    have hq0 := hq.nonneg
    refine ⟨?_,?_,?_⟩
    · apply (qBoundedJets_tiltedAverage_sub 4 hf (by norm_num) le_rfl hg hm (p k).2 hv hcurv).mono
      calc
        _ ≤ C*tiltedDifferenceCoefficient 4 B*e := by gcongr
        _ ≤ K*C*e := by
          have H := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hD₄K hg0) he0
          nlinarith only [H]
    · apply (qBoundedJets_firstTiltedAverageSource_sub_energy (e := e)
        (hf.of_le (by norm_num : 5 ≤ 6)) hf₁ (hg.of_le (by norm_num : 4 ≤ 6)) ha
        hR.le le_rfl hm hentry.2.2.1 (p k).2 (deriv (fun t => (p t).2) k) hv hcurv
        (by dsimp only [e,windowVariationEnergy]; nlinarith only [sq_nonneg ‖deriv (deriv (fun t => (p t).2)) k‖])).mono
      have H := add_le_add (mul_le_mul_of_nonneg_right hD₂K ha0')
        (mul_le_mul_of_nonneg_right hT₁K hg0)
      have H' := mul_le_mul_of_nonneg_right H he0
      change (A*tiltedDifferenceCoefficient 2 B+T₁*C)*e ≤ K*(C+A)*e
      nlinarith only [H']
    · intro x
      apply (abs_secondMovingAverageSource_sub_energy (e := e) (hf.of_le (by norm_num : 3 ≤ 6))
        (hf₁.of_le (by norm_num : 1 ≤ 3)) hf₂ (hg.of_le (by norm_num : 3 ≤ 6))
        (ha.of_le (by norm_num : 2 ≤ 4)) hq hm hentry.2.2.1 hentry.2.2.2
        (p k).2 (deriv (fun t => (p t).2) k) (deriv (deriv (fun t => (p t).2)) k)
        le_rfl he1 x).trans
      have H := add_le_add (mul_le_mul_of_nonneg_right hBK hq0)
        (mul_le_mul_of_nonneg_right hT₂K (add_nonneg hg0 ha0'))
      have H' := mul_le_mul_of_nonneg_right H he0
      change ((1+B)^2*Q+T₂*(C+A))*e ≤ K*(C+A+Q)*e
      nlinarith only [H']
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
