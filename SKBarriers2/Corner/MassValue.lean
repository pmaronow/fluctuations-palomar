module

public import SKBarriers2.Corner.MassSensitivityC2
public import SKBarriers2.Corner.TerminalJets

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def tiltedDifferenceCoefficient : ℕ → ℝ → ℝ
  | 0, B => (1+B)^2
  | n+1, B => tiltedDifferenceCoefficient n B+(1+B)^2+|covarianceJetCoefficient n B*B|

theorem tiltedDifferenceCoefficient_base_le (n : ℕ) (B : ℝ) :
    (1+B)^2 ≤ tiltedDifferenceCoefficient n B := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    dsimp only [tiltedDifferenceCoefficient]
    linarith only [ih,sq_nonneg (1+B),abs_nonneg (covarianceJetCoefficient n B*B)]

theorem tiltedDifferenceCoefficient_nonneg (n : ℕ) (B : ℝ) :
    0 ≤ tiltedDifferenceCoefficient n B :=
  (sq_nonneg (1+B)).trans (tiltedDifferenceCoefficient_base_le n B)

theorem qBoundedJets_tiltedAverage_sub (n : ℕ) {r : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hn : n+2 ≤ r)
    (hg : QBoundedJets (n+2) C g) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets n (C*tiltedDifferenceCoefficient n B*‖v‖^2)
      (fun x => tiltedAverage m v f g x-g x) := by
  have hB : 0 ≤ B := hf.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hbase (x : E) : |tiltedAverage m v f g x-g x| ≤ C*(1+B)^2*‖v‖^2 :=
    abs_noiseMean_sub_le hf hr (qBoundedJets_iff_qBddSmooth.mp hg).potential (by omega) hm v x hv
  induction n generalizing C g with
  | zero =>
    refine ⟨by dsimp only [tiltedDifferenceCoefficient]; positivity,
      ((tiltedAverage_smooth 0 hf hr (by omega) (hg.of_le (by omega)) m v).sub
        (hg.smooth.of_le (by norm_num))),?_⟩
    intro j hj x
    have hj0 : j = 0 := by omega
    subst j
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,tiltedDifferenceCoefficient] using hbase x
  | succ n ih =>
    have hK : 0 ≤ C*tiltedDifferenceCoefficient (n+1) B*‖v‖^2 :=
      mul_nonneg (mul_nonneg hC (tiltedDifferenceCoefficient_nonneg _ _)) (sq_nonneg _)
    have hgl : QBoundedJets (n+1) C g := hg.of_le (by omega)
    have hgs : QBddSmooth 1 C g := qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega))
    have hs : ContDiff ℝ (n+1) (fun x => tiltedAverage m v f g x-g x) :=
      (tiltedAverage_smooth (n+1) hf hr (by omega) hgl m v).sub hgl.smooth
    apply QBoundedJets.of_directional hK hs
    · intro x
      exact (hbase x).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (tiltedDifferenceCoefficient_base_le _ _) hC) (sq_nonneg _))
    · intro w hw
      have hdg : QBoundedJets (n+2) C (fun x => fderiv ℝ g x w) := by
        simpa only [hw,mul_one] using hg.derivativeJets.apply_const w
      have hscore : QBoundedJets (n+1) B (fun x => fderiv ℝ f x w) := by
        simpa only [hw,mul_one] using (hf.of_le (by omega : n+2 ≤ r)).derivativeJets.apply_const w
      have hD := ih (by omega) hdg hC (fun x =>
        abs_noiseMean_sub_le hf hr (qBoundedJets_iff_qBddSmooth.mp hdg).potential
          (by omega) hm v x hv)
      have hCov := qBoundedJets_spatialCovariance n hf hr (by omega)
        (hg.of_le (by omega : n+1 ≤ n+3)) hscore hm v hsmall
      have hMCov := (hCov.const_smul m).mono (mul_le_of_le_one_left hCov.nonneg (by
        rw [abs_of_nonneg hm.1]
        exact hm.2))
      have hSum := hD.add hMCov
      have he : (fun x => fderiv ℝ (fun y => tiltedAverage m v f g y-g y) x w) =
          fun x => (tiltedAverage m v f (fun y => fderiv ℝ g y w) x-fderiv ℝ g x w)+
            m*spatialCovariance m v f g (fun y => fderiv ℝ f y w) x := by
        funext x
        rw [fderiv_fun_sub
          ((tiltedAverage_smooth (n+1) hf hr (by omega) hgl m v).differentiable (by simp) x)
          (hgl.smooth.differentiable (by simp) x)]
        change fderiv ℝ (tiltedAverage m v f g) x w-fderiv ℝ g x w = _
        rw [fderiv_tiltedAverage_apply hf hr hgs,
          spatialCovariance_eq hf hr hgs (qBoundedJets_iff_qBddSmooth.mp (hscore.of_le (by omega)))]
        dsimp only [tiltedAverage,noiseMean]
        ring
      rw [he]
      apply hSum.mono
      have hcov : covarianceJetCoefficient n B*B ≤ |covarianceJetCoefficient n B*B| := le_abs_self _
      dsimp only [tiltedDifferenceCoefficient]
      nlinarith only [mul_nonneg hC (sq_nonneg ‖v‖),hcov,
        mul_le_mul_of_nonneg_right hcov (mul_nonneg hC (sq_nonneg ‖v‖)),sq_nonneg (1+B),
        mul_nonneg (sq_nonneg (1+B)) (mul_nonneg hC (sq_nonneg ‖v‖))]

theorem abs_step_sub_le {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (v x : E) (hv : ‖v‖ ≤ 1) :
    |vectorStep m v f x-f x| ≤ B*(1+B)^2*‖v‖^2 := by
  have hc := continuous_noiseMean_mass hf hr v x
  have hcont : Continuous (fun t : ℝ => noiseMean (t*m) v f x (fun u => f (x+u • v))) :=
    hc.comp (continuous_id.mul continuous_const)
  have he : vectorStep m v f x-f x =
      ∫ t : ℝ in 0..1, noiseMean (t*m) v f x (fun u => f (x+u • v))-f x := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f x) volume 0 1),
      ← step_eq_integral_noiseMean hf hr]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  rw [he]
  have hbound (t : ℝ) (ht : t ∈ uIoc (0:ℝ) 1) :
      ‖noiseMean (t*m) v f x (fun u => f (x+u • v))-f x‖ ≤ B*(1+B)^2*‖v‖^2 := by
    rw [uIoc_of_le zero_le_one] at ht
    have htm : t*m ∈ Icc (0:ℝ) 1 :=
      ⟨mul_nonneg ht.1.le hm.1,(mul_le_of_le_one_left hm.1 ht.2).trans hm.2⟩
    simpa only [Real.norm_eq_abs] using abs_noiseMean_sub_le hf hr hf hr htm v x hv
  simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

def spatialStepDifferenceCoefficient (n : ℕ) (B : ℝ) : ℝ :=
  B*(1+B)^2+B*tiltedDifferenceCoefficient n B

theorem spatialStepDifferenceCoefficient_nonneg (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ spatialStepDifferenceCoefficient n B := by
  exact add_nonneg (by positivity) (mul_nonneg hB (tiltedDifferenceCoefficient_nonneg _ _))

theorem qBoundedJets_step_sub (n : ℕ) {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n+3) B f) {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) (hsmall : m*(B*‖v‖^2) ≤ 1/2) :
    QBoundedJets (n+1) (spatialStepDifferenceCoefficient n B*‖v‖^2)
      (fun x => vectorStep m v f x-f x) := by
  have hB : 0 ≤ B := hf.nonneg
  have hK := spatialStepDifferenceCoefficient_nonneg n hB
  apply QBoundedJets.of_directional (mul_nonneg hK (sq_nonneg _))
    (((contDiff_step hf m v).of_le (by norm_cast; omega)).sub
      (hf.smooth.of_le (by norm_cast; omega)))
  · intro x
    exact (abs_step_sub_le hf (by omega) hm v x hv).trans (by
      unfold spatialStepDifferenceCoefficient
      nlinarith only [mul_nonneg (mul_nonneg hB (tiltedDifferenceCoefficient_nonneg n B)) (sq_nonneg ‖v‖)])
  · intro w hw
    have hd : QBoundedJets (n+2) B (fun x => fderiv ℝ f x w) := by
      simpa only [hw,mul_one] using hf.derivativeJets.apply_const w
    have H := qBoundedJets_tiltedAverage_sub n hf (by omega) (by omega) hd hm v hv hsmall
    have he : (fun x => fderiv ℝ (fun y => vectorStep m v f y-f y) x w) =
        fun x => tiltedAverage m v f (fun y => fderiv ℝ f y w) x-fderiv ℝ f x w := by
      funext x
      rw [fderiv_fun_sub ((contDiff_step hf m v).differentiable (by simp) x)
        (hf.smooth.differentiable (by simp) x)]
      change fderiv ℝ (vectorStep m v f) x w-fderiv ℝ f x w = _
      rw [fderiv_step_apply hf (by omega)]
      rfl
    rw [he]
    apply H.mono
    unfold spatialStepDifferenceCoefficient
    nlinarith only [mul_nonneg (mul_nonneg hB (sq_nonneg (1+B))) (sq_nonneg ‖v‖)]

def SpatialChainJets (r : ℕ) (B : ℝ) (l : List (ℝ × E)) (f : E → ℝ) : Prop :=
  ∀ n : ℕ, QPotential r B (vectorIncrementChain (l.drop n) f)

theorem qBoundedJets_chain_sub {B : ℝ} {f : E → ℝ} (l : List (ℝ × E))
    (hjets : SpatialChainJets 5 B l f)
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1)
    (hv : ∀ p ∈ l, ‖p.2‖ ≤ 1 ∧ p.1*(B*‖p.2‖^2) ≤ 1/2) :
    QBoundedJets 3 (spatialStepDifferenceCoefficient 2 B*chainEnergy l)
      (fun x => vectorIncrementChain l f x-f x) := by
  induction l with
  | nil =>
    refine ⟨by simp [chainEnergy],((hjets 0).smooth.sub (hjets 0).smooth).of_le (by norm_num),?_⟩
    intro j hj x
    have he : (fun x => vectorIncrementChain [] f x-f x) = fun _ => (0:ℝ) := by
      funext x
      exact sub_self _
    rw [he]
    simp [chainEnergy]
  | cons p l ih =>
    have ht : SpatialChainJets 5 B l f := fun n => by simpa only [List.drop_succ_cons] using hjets (n+1)
    have hhead := qBoundedJets_step_sub 2 (ht 0) (hm p (by simp)) p.2
      (hv p (by simp)).1 (hv p (by simp)).2
    have htail := ih ht (fun q hq => hm q (by simp [hq])) (fun q hq => hv q (by simp [hq]))
    have hsum := hhead.add htail
    have he : (fun x => vectorIncrementChain (p::l) f x-f x) =
        fun x => (vectorStep p.1 p.2 (vectorIncrementChain l f) x-vectorIncrementChain l f x)+
          (vectorIncrementChain l f x-f x) := by
      funext x
      dsimp only [vectorIncrementChain]
      ring
    rw [he,chainEnergy_cons]
    simpa only [List.drop_zero,mul_add] using hsum

theorem abs_tiltedAverage_sub_le {r : ℕ} {B A C D : ℝ} {f g a : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hg : Continuous g) (ha : Continuous a)
    (hgb : ∀ x, |g x| ≤ C) (hab : ∀ x, |a x| ≤ D)
    (hga : ∀ x, |g x-a x| ≤ A) (m : ℝ) (v x : E) :
    |tiltedAverage m v f g x-tiltedAverage m v f a x| ≤ A := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
  have hiG : Integrable (fun t : ℝ => g (x+t • v)) μ :=
    Integrable.of_bound (hg.comp hc).aestronglyMeasurable C (ae_of_all _ (fun t => hgb _))
  have hiA : Integrable (fun t : ℝ => a (x+t • v)) μ :=
    Integrable.of_bound (ha.comp hc).aestronglyMeasurable D (ae_of_all _ (fun t => hab _))
  change |(∫ t : ℝ, g (x+t • v) ∂μ)-(∫ t : ℝ, a (x+t • v) ∂μ)| ≤ A
  rw [← integral_sub hiG hiA]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := fun t : ℝ => g (x+t • v)-a (x+t • v))
      (C := A) (ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hga (x+t • v)))

theorem abs_vectorIncrementAverage_le {B C : ℝ} {f g : E → ℝ}
    (l : List (ℝ × E)) (hjets : SpatialChainJets 5 B l f) (hg : ∀ x, |g x| ≤ C) (x : E) :
    |vectorIncrementAverage l f g x| ≤ C := by
  induction l generalizing x with
  | nil => exact hg x
  | cons p l ih =>
    have ht : SpatialChainJets 5 B l f := fun n => by
      simpa only [List.drop_succ_cons] using hjets (n+1)
    change |tiltedAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f g) x| ≤ C
    simpa only [Real.norm_eq_abs,List.drop_zero] using norm_tiltedAverage_le (ht 0) (by norm_num)
      (g := vectorIncrementAverage l f g) (C := C)
      (fun y => by simpa only [Real.norm_eq_abs] using ih ht y) p.1 p.2 x

def pathGenerator (m : ℝ) (v : E) (f g : E → ℝ) (x : E) : ℝ :=
  m*fderiv ℝ f x v*fderiv ℝ g x v+directionalJet v 2 g x/2

theorem qBoundedJets_pathGenerator {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v : E) :
    QBoundedJets 2 ((4*B+1)*C*‖v‖^2) (pathGenerator m v f g) := by
  have hdf := hf.derivativeJets.apply_const v
  have hdg := (hg.of_le (by norm_num : 3≤4)).derivativeJets.apply_const v
  have hmul := ((hdf.mul hdg).const_smul m).mono (mul_le_of_le_one_left (hdf.mul hdg).nonneg (by
    rw [abs_of_nonneg hm.1]
    exact hm.2))
  have hdd : QBoundedJets 2 (C*‖v‖^2) (directionalJet v 2 g) :=
    qBoundedJets_iff_qBddSmooth.mpr (directionalJet_smooth 1
      (qBoundedJets_iff_qBddSmooth.mp hg).potential v)
  have hhalf := (hdd.const_smul (1/2:ℝ)).mono (mul_le_of_le_one_left hdd.nonneg (by norm_num))
  have hsum := hmul.add hhalf
  have he : pathGenerator m v f g = fun x =>
      m • (fderiv ℝ f x v*fderiv ℝ g x v)+(1/2:ℝ) • directionalJet v 2 g x := by
    funext x
    simp only [pathGenerator,smul_eq_mul]
    ring
  rw [he]
  convert hsum using 1
  norm_num
  ring

def pathGeneratorSum (f g : E → ℝ) : List (ℝ × E) → E → ℝ
  | [], _ => 0
  | p::l, x => pathGenerator p.1 p.2 f g x+pathGeneratorSum f g l x

theorem qBoundedJets_pathGeneratorSum {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 4 C g) (l : List (ℝ × E))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) :
    QBoundedJets 2 ((4*B+1)*C*chainEnergy l) (pathGeneratorSum f g l) := by
  induction l with
  | nil =>
    refine ⟨by simp [chainEnergy],contDiff_const,?_⟩
    intro j hj x
    simp [pathGeneratorSum,chainEnergy]
  | cons p l ih =>
    have hhead := qBoundedJets_pathGenerator hf hg (hm p (by simp)) p.2
    have htail := ih (fun q hq => hm q (by simp [hq]))
    simpa only [pathGeneratorSum,chainEnergy_cons,mul_add] using hhead.add htail

theorem abs_vectorIncrementAverage_sub_le {B C : ℝ} {f g : E → ℝ}
    (l : List (ℝ × E)) (hjets : SpatialChainJets 5 B l f) (hg : QBoundedJets 2 C g)
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) (hv : ∀ p ∈ l, ‖p.2‖ ≤ 1) (x : E) :
    |vectorIncrementAverage l f g x-g x| ≤ C*(1+B)^2*chainEnergy l := by
  have hC : 0 ≤ C := hg.nonneg
  induction l generalizing x with
  | nil => simp only [vectorIncrementAverage,sub_self,abs_zero,chainEnergy,List.map_nil,List.sum_nil,mul_zero,le_refl]
  | cons p l ih =>
    have ht : SpatialChainJets 5 B l f := fun n => by
      simpa only [List.drop_succ_cons] using hjets (n+1)
    have hterminal : QPotential 5 B f := by simpa only [List.drop_length,vectorIncrementChain] using ht l.length
    have hgreg := vectorIncrementAverage_regular l (hterminal.boundedDerivs (by norm_num))
      hg.smooth.continuous ((qBoundedJets_iff_qBddSmooth.mp hg).potential.boundedDerivs (by norm_num)).hasExpGrowth
    have H := abs_tiltedAverage_sub_le (ht 0) (by norm_num) hgreg.1 hg.smooth.continuous
      (fun y => abs_vectorIncrementAverage_le l ht (fun z => by simpa only [Real.norm_eq_abs] using hg.norm_le z) y)
      (fun y => by simpa only [Real.norm_eq_abs] using hg.norm_le y)
      (fun y => ih ht (fun q hq => hm q (by simp [hq])) (fun q hq => hv q (by simp [hq])) y)
      p.1 p.2 x
    have Hstep := abs_noiseMean_sub_le (ht 0) (by norm_num)
      (qBoundedJets_iff_qBddSmooth.mp hg).potential (by norm_num) (hm p (by simp)) p.2 x (hv p (by simp))
    change |tiltedAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f g) x-g x| ≤ _
    have he : tiltedAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f g) x-g x =
        (tiltedAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f g) x-
          tiltedAverage p.1 p.2 (vectorIncrementChain l f) g x)+
        (tiltedAverage p.1 p.2 (vectorIncrementChain l f) g x-g x) := by ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add H Hstep).trans_eq (by rw [chainEnergy_cons]; ring))

private theorem abs_pathGenerator_sub_potential_le {B C H : ℝ} {f F g : E → ℝ}
    (hf : QPotential 5 B f) (hF : QPotential 5 B F)
    (hdiff : QBoundedJets 3 H (fun x => F x-f x)) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) :
    |pathGenerator m v F g x-pathGenerator m v f g x| ≤ H*C*‖v‖^2 := by
  have hH : 0 ≤ H := hdiff.nonneg
  have hC : 0 ≤ C := hg.nonneg
  have hD := (qBoundedJets_iff_qBddSmooth.mp hdiff).potential.directional_le (by norm_num) x v
  rw [fderiv_fun_sub (hF.smooth.differentiable (by norm_num) x)
    (hf.smooth.differentiable (by norm_num) x)] at hD
  change |fderiv ℝ F x v-fderiv ℝ f x v| ≤ H*‖v‖ at hD
  have hG := (qBoundedJets_iff_qBddSmooth.mp hg).potential.directional_le (by norm_num) x v
  have he : pathGenerator m v F g x-pathGenerator m v f g x =
      m*(fderiv ℝ F x v-fderiv ℝ f x v)*fderiv ℝ g x v := by
    unfold pathGenerator
    ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg hm.1]
  calc
    _ ≤ 1*(H*‖v‖)*(C*‖v‖) := by gcongr; exact hm.2
    _ = _ := by ring

def pathValueExpansionCoefficient (B : ℝ) : ℝ :=
  pathExpansionConstant B+spatialStepDifferenceCoefficient 2 B+(4*B+1)*(1+B)^2

theorem pathValueExpansionCoefficient_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ pathValueExpansionCoefficient B := by
  unfold pathValueExpansionCoefficient
  exact add_nonneg (add_nonneg (pathExpansionConstant_nonneg hB)
    (spatialStepDifferenceCoefficient_nonneg _ hB)) (by positivity)

theorem abs_vectorIncrementAverage_firstOrder_le {B C : ℝ} {f g : E → ℝ}
    (l : List (ℝ × E)) (hjets : SpatialChainJets 5 B l f) (hg : QBoundedJets 4 C g)
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1)
    (hv : ∀ p ∈ l, ‖p.2‖ ≤ 1 ∧ p.1*(B*‖p.2‖^2) ≤ 1/2) (x : E) :
    |vectorIncrementAverage l f g x-g x-pathGeneratorSum f g l x| ≤
      C*pathValueExpansionCoefficient B*(chainEnergy l)^2 := by
  have hC : 0 ≤ C := hg.nonneg
  have hB : 0 ≤ B := (hjets 0).nonneg
  have hP : 0 ≤ pathValueExpansionCoefficient B := pathValueExpansionCoefficient_nonneg hB
  have hK : 0 ≤ spatialStepDifferenceCoefficient 2 B := spatialStepDifferenceCoefficient_nonneg _ hB
  have hPath : 0 ≤ pathExpansionConstant B := pathExpansionConstant_nonneg hB
  induction l generalizing x with
  | nil => simp only [vectorIncrementAverage,pathGeneratorSum,sub_self,abs_zero,
      chainEnergy,List.map_nil,List.sum_nil,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  | cons p l ih =>
    have ht : SpatialChainJets 5 B l f := fun n => by
      simpa only [List.drop_succ_cons] using hjets (n+1)
    have hf : QPotential 5 B f := by simpa only [List.drop_length,vectorIncrementChain] using ht l.length
    have hmT : ∀ q ∈ l, q.1 ∈ Icc (0:ℝ) 1 := fun q hq => hm q (by simp [hq])
    have hvT : ∀ q ∈ l, ‖q.2‖ ≤ 1 ∧ q.1*(B*‖q.2‖^2) ≤ 1/2 :=
      fun q hq => hv q (by simp [hq])
    have hmp := hm p (by simp)
    have hvp := hv p (by simp)
    let S := pathGeneratorSum f g l
    have hS : QBoundedJets 2 ((4*B+1)*C*chainEnergy l) S :=
      qBoundedJets_pathGeneratorSum (hf.of_le (by norm_num)) hg l hmT
    have hg2 : QBoundedJets 2 C g := hg.of_le (by norm_num)
    have hgs := hg2.add hS
    have hgc := vectorIncrementAverage_regular l (hf.boundedDerivs (by norm_num))
      hg.smooth.continuous ((qBoundedJets_iff_qBddSmooth.mp hg2).potential.boundedDerivs (by norm_num)).hasExpGrowth
    have hprop := abs_tiltedAverage_sub_le (ht 0) (by norm_num) hgc.1 hgs.smooth.continuous
      (fun y => abs_vectorIncrementAverage_le l ht (fun z => by simpa only [Real.norm_eq_abs] using hg.norm_le z) y)
      (fun y => by simpa only [Real.norm_eq_abs] using hgs.norm_le y)
      (fun y => by
        have H := ih ht hmT hvT y
        convert H using 1
        congr 1
        dsimp only [S]
        ring) p.1 p.2 x
    have hlocal : |tiltedAverage p.1 p.2 (vectorIncrementChain l f) g x-g x-
        pathGenerator p.1 p.2 (vectorIncrementChain l f) g x| ≤
        C*pathExpansionConstant B*‖p.2‖^4 := by
      have H := abs_noiseMean_generator_remainder_le (ht 0) (by norm_num)
        (qBoundedJets_iff_qBddSmooth.mp hg).potential (by norm_num) hmp p.2 x hvp.1
      simp only [List.drop_zero] at H
      convert H using 1
      congr 1
      dsimp only [pathGenerator,tiltedAverage,noiseMean,List.drop_zero]
      ring
    have hcomp := abs_pathGenerator_sub_potential_le hf (ht 0)
      (qBoundedJets_chain_sub l ht hmT hvT) hg hmp p.2 x
    have hstep := (abs_sub_le
      (tiltedAverage p.1 p.2 (vectorIncrementChain l f) g x-g x)
      (pathGenerator p.1 p.2 (vectorIncrementChain l f) g x)
      (pathGenerator p.1 p.2 f g x)).trans (add_le_add hlocal hcomp)
    have hweak := abs_noiseMean_sub_le (ht 0) (by norm_num) (qBoundedJets_iff_qBddSmooth.mp hS).potential (by norm_num)
      hmp p.2 x hvp.1
    have hadd : tiltedAverage p.1 p.2 (vectorIncrementChain l f) (fun y => g y+S y) x =
        tiltedAverage p.1 p.2 (vectorIncrementChain l f) g x+
          tiltedAverage p.1 p.2 (vectorIncrementChain l f) S x := by
      exact congrFun (vectorStepAverage_add ((ht 0).boundedDerivs (by norm_num))
        hg.smooth.continuous hS.smooth.continuous
        ((qBoundedJets_iff_qBddSmooth.mp hg2).potential.boundedDerivs (by norm_num)).hasExpGrowth
        ((qBoundedJets_iff_qBddSmooth.mp hS).potential.boundedDerivs (by norm_num)).hasExpGrowth p.1 p.2) x
    have he : vectorIncrementAverage (p::l) f g x-g x-pathGeneratorSum f g (p::l) x =
        (tiltedAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f g) x-
          tiltedAverage p.1 p.2 (vectorIncrementChain l f) (fun y => g y+S y) x)+
        (tiltedAverage p.1 p.2 (vectorIncrementChain l f) g x-g x-pathGenerator p.1 p.2 f g x)+
        (tiltedAverage p.1 p.2 (vectorIncrementChain l f) S x-S x) := by
      change _-g x-(pathGenerator p.1 p.2 f g x+S x) = _
      rw [hadd]
      change tiltedAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f g) x-
        g x-(pathGenerator p.1 p.2 f g x+S x) = _
      ring
    rw [he]
    calc
      _ ≤ |tiltedAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f g) x-
            tiltedAverage p.1 p.2 (vectorIncrementChain l f) (fun y => g y+S y) x|+
          |tiltedAverage p.1 p.2 (vectorIncrementChain l f) g x-g x-pathGenerator p.1 p.2 f g x|+
          |tiltedAverage p.1 p.2 (vectorIncrementChain l f) S x-S x| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ C*pathValueExpansionCoefficient B*(chainEnergy l)^2+
          (C*pathExpansionConstant B*‖p.2‖^4+
            (spatialStepDifferenceCoefficient 2 B*chainEnergy l)*C*‖p.2‖^2)+
          ((4*B+1)*C*chainEnergy l)*(1+B)^2*‖p.2‖^2 :=
        add_le_add (add_le_add hprop hstep) hweak
      _ ≤ _ := by
        have hE : 0 ≤ chainEnergy l := chainEnergy_nonneg l
        rw [chainEnergy_cons]
        unfold pathValueExpansionCoefficient
        nlinarith only [
          show 0 ≤ C*spatialStepDifferenceCoefficient 2 B*‖p.2‖^4 by positivity,
          show 0 ≤ C*(4*B+1)*(1+B)^2*‖p.2‖^4 by positivity,
          show 0 ≤ C*(2*pathExpansionConstant B+spatialStepDifferenceCoefficient 2 B+
            (4*B+1)*(1+B)^2)*chainEnergy l*‖p.2‖^2 by positivity]

theorem fderiv_chain_apply_eq_average {B : ℝ} {f : E → ℝ}
    (l : List (ℝ × E)) (hjets : SpatialChainJets 5 B l f) (w x : E) :
    fderiv ℝ (vectorIncrementChain l f) x w =
      vectorIncrementAverage l f (fun y => fderiv ℝ f y w) x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    have ht : SpatialChainJets 5 B l f := fun n => by
      simpa only [List.drop_succ_cons] using hjets (n+1)
    have he : (fun y => fderiv ℝ (vectorIncrementChain l f) y w) =
        vectorIncrementAverage l f (fun y => fderiv ℝ f y w) := funext (fun y => ih ht y)
    change fderiv ℝ (vectorStep p.1 p.2 (vectorIncrementChain l f)) x w = _
    have ht0 : QPotential 5 B (vectorIncrementChain l f) := by simpa only [List.drop_zero] using ht 0
    rw [fderiv_step_apply ht0 (by norm_num)]
    change tiltedAverage p.1 p.2 (vectorIncrementChain l f)
      (fun y => fderiv ℝ (vectorIncrementChain l f) y w) x = _
    rw [he]
    rfl

private theorem directional_difference {B H : ℝ} {f F : E → ℝ}
    (hf : QPotential 5 B f) (hF : QPotential 5 B F)
    (hdiff : QBoundedJets 3 H (fun x => F x-f x)) (w : E) :
    QBoundedJets 2 (H*‖w‖) (fun x => fderiv ℝ F x w-fderiv ℝ f x w) := by
  have H := hdiff.derivativeJets.apply_const w
  have he : (fun x => fderiv ℝ F x w-fderiv ℝ f x w) =
      fun x => fderiv ℝ (fun y => F y-f y) x w := by
    funext x
    rw [fderiv_fun_sub (hF.smooth.differentiable (by norm_num) x)
      (hf.smooth.differentiable (by norm_num) x)]
    rfl
  rw [he]
  exact H

private theorem abs_square_firstOrder_le {a A b H R U : ℝ}
    (_hH : 0 ≤ H) (_hR : 0 ≤ R) (hU : 0 ≤ U)
    (hd : |A-a| ≤ H) (ha : |a| ≤ U) (hr : |A-a-b| ≤ R) :
    |A^2-a^2-2*a*b| ≤ H^2+2*U*R := by
  have he : A^2-a^2-2*a*b = (A-a)^2+2*a*(A-a-b) := by ring
  rw [he]
  calc
    _ ≤ |(A-a)^2| + |2*a*(A-a-b)| := abs_add_le _ _
    _ ≤ H^2+2*U*R := by
      simp only [abs_pow,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      gcongr

def firstOrderPathEnergy (front tail : List (ℝ × E)) (f : E → ℝ) (w x : E) : ℝ :=
  (fderiv ℝ f x w)^2+
    2*fderiv ℝ f x w*pathGeneratorSum f (fun y => fderiv ℝ f y w) tail x+
    pathGeneratorSum f (fun y => (fderiv ℝ f y w)^2) front x

theorem abs_chain_gradient_sq_firstOrder_le {B : ℝ} {f : E → ℝ}
    (l : List (ℝ × E)) (hjets : SpatialChainJets 5 B l f)
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1)
    (hv : ∀ p ∈ l, ‖p.2‖ ≤ 1 ∧ p.1*(B*‖p.2‖^2) ≤ 1/2) (w x : E) :
    |(fderiv ℝ (vectorIncrementChain l f) x w)^2-(fderiv ℝ f x w)^2-
      2*fderiv ℝ f x w*pathGeneratorSum f (fun y => fderiv ℝ f y w) l x| ≤
      ((spatialStepDifferenceCoefficient 2 B)^2+2*B^2*pathValueExpansionCoefficient B)*
        ‖w‖^2*(chainEnergy l)^2 := by
  have hf : QPotential 5 B f := by simpa only [List.drop_length,vectorIncrementChain] using hjets l.length
  have hB : 0 ≤ B := hf.nonneg
  have hK : 0 ≤ spatialStepDifferenceCoefficient 2 B := spatialStepDifferenceCoefficient_nonneg _ hB
  have hP : 0 ≤ pathValueExpansionCoefficient B := pathValueExpansionCoefficient_nonneg hB
  have hE : 0 ≤ chainEnergy l := chainEnergy_nonneg l
  have hd : QBoundedJets 4 (B*‖w‖) (fun y => fderiv ℝ f y w) := hf.derivativeJets.apply_const w
  have hprox := directional_difference hf (hjets 0) (qBoundedJets_chain_sub l hjets hm hv) w
  have hdiff : |fderiv ℝ (vectorIncrementChain l f) x w-fderiv ℝ f x w| ≤
      (spatialStepDifferenceCoefficient 2 B*chainEnergy l)*‖w‖ := by
    simpa only [Real.norm_eq_abs,List.drop_zero] using hprox.norm_le x
  have hfirst := abs_vectorIncrementAverage_firstOrder_le l hjets hd hm hv x
  rw [← fderiv_chain_apply_eq_average l hjets w x] at hfirst
  have H := abs_square_firstOrder_le
    (by positivity : 0 ≤ (spatialStepDifferenceCoefficient 2 B*chainEnergy l)*‖w‖)
    (by positivity : 0 ≤ (B*‖w‖)*pathValueExpansionCoefficient B*(chainEnergy l)^2)
    (by positivity : 0 ≤ B*‖w‖) hdiff (hf.directional_le (by norm_num) x w) hfirst
  exact H.trans_eq (by ring)

theorem qBoundedJets_chain_gradient_sq_sub {B : ℝ} {f : E → ℝ}
    (l : List (ℝ × E)) (hjets : SpatialChainJets 5 B l f)
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1)
    (hv : ∀ p ∈ l, ‖p.2‖ ≤ 1 ∧ p.1*(B*‖p.2‖^2) ≤ 1/2) (w : E) :
    QBoundedJets 2 (8*B*spatialStepDifferenceCoefficient 2 B*chainEnergy l*‖w‖^2)
      (fun x => (fderiv ℝ (vectorIncrementChain l f) x w)^2-(fderiv ℝ f x w)^2) := by
  have hf : QPotential 5 B f := by simpa only [List.drop_length,vectorIncrementChain] using hjets l.length
  have hdiff := directional_difference hf (hjets 0) (qBoundedJets_chain_sub l hjets hm hv) w
  have hD₁ := ((hjets 0).of_le (by norm_num : 3≤5)).derivativeJets.apply_const w
  have hD₂ := (hf.of_le (by norm_num : 3≤5)).derivativeJets.apply_const w
  have hprod := hdiff.mul (hD₁.add hD₂)
  have he : (fun x => (fderiv ℝ (vectorIncrementChain l f) x w)^2-(fderiv ℝ f x w)^2) =
      fun x => (fderiv ℝ (vectorIncrementChain l f) x w-fderiv ℝ f x w)*
        (fderiv ℝ (vectorIncrementChain l f) x w+fderiv ℝ f x w) := by
    funext x
    ring
  rw [he]
  convert hprod using 1
  · norm_num
    ring
  · simp only [List.drop_zero]

private theorem abs_pathGeneratorSum_sub_potential_le {B C H : ℝ} {f F g : E → ℝ}
    (hf : QPotential 5 B f) (hF : QPotential 5 B F)
    (hdiff : QBoundedJets 3 H (fun x => F x-f x)) (hg : QBoundedJets 4 C g)
    (l : List (ℝ × E)) (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) (x : E) :
    |pathGeneratorSum F g l x-pathGeneratorSum f g l x| ≤ H*C*chainEnergy l := by
  induction l with
  | nil => simp [pathGeneratorSum,chainEnergy]
  | cons p l ih =>
    have hp := abs_pathGenerator_sub_potential_le hf hF hdiff hg (hm p (by simp)) p.2 x
    have ht := ih (fun q hq => hm q (by simp [hq]))
    have he : pathGeneratorSum F g (p::l) x-pathGeneratorSum f g (p::l) x =
        (pathGenerator p.1 p.2 F g x-pathGenerator p.1 p.2 f g x)+
        (pathGeneratorSum F g l x-pathGeneratorSum f g l x) := by
      simp only [pathGeneratorSum]
      ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add hp ht).trans_eq (by rw [chainEnergy_cons]; ring))

theorem abs_pathEnergy_firstOrder_le {B : ℝ} {f : E → ℝ}
    (front tail : List (ℝ × E)) (p : ℝ × E)
    (hinner : SpatialChainJets 5 B (p::tail) f)
    (hfront : SpatialChainJets 5 B front (vectorIncrementChain (p::tail) f))
    (hmI : ∀ q ∈ p::tail, q.1 ∈ Icc (0:ℝ) 1)
    (hvI : ∀ q ∈ p::tail, ‖q.2‖ ≤ 1 ∧ q.1*(B*‖q.2‖^2) ≤ 1/2)
    (hmF : ∀ q ∈ front, q.1 ∈ Icc (0:ℝ) 1)
    (hvF : ∀ q ∈ front, ‖q.2‖ ≤ 1 ∧ q.1*(B*‖q.2‖^2) ≤ 1/2) (w x : E) :
    |vectorIncrementAverage front (vectorIncrementChain (p::tail) f)
        (fun y => (fderiv ℝ (vectorIncrementChain tail f) y w)^2) x-
      firstOrderPathEnergy front tail f w x| ≤
      ((spatialStepDifferenceCoefficient 2 B)^2+2*B^2*pathValueExpansionCoefficient B)*
        ‖w‖^2*(chainEnergy tail)^2+
      (16*B^2*‖w‖^2)*pathValueExpansionCoefficient B*(chainEnergy front)^2+
      (spatialStepDifferenceCoefficient 2 B*chainEnergy (p::tail))*(16*B^2*‖w‖^2)*chainEnergy front+
      (8*B*spatialStepDifferenceCoefficient 2 B*chainEnergy tail*‖w‖^2)*(1+B)^2*chainEnergy front := by
  let F := vectorIncrementChain (p::tail) f
  let T := vectorIncrementChain tail f
  let ψ := fun y => (fderiv ℝ f y w)^2
  let δ := fun y => (fderiv ℝ T y w)^2-ψ y
  have ht : SpatialChainJets 5 B tail f := fun n => by
    simpa only [List.drop_succ_cons] using hinner (n+1)
  have hf : QPotential 5 B f := by simpa only [List.drop_length,vectorIncrementChain] using ht tail.length
  have hF : QPotential 5 B F := hinner 0
  have hT : QPotential 5 B T := ht 0
  have hmT : ∀ q ∈ tail, q.1 ∈ Icc (0:ℝ) 1 := fun q hq => hmI q (by simp [hq])
  have hvT : ∀ q ∈ tail, ‖q.2‖ ≤ 1 ∧ q.1*(B*‖q.2‖^2) ≤ 1/2 :=
    fun q hq => hvI q (by simp [hq])
  have hψ : QBoundedJets 4 (16*B^2*‖w‖^2) ψ := by
    have H := (hf.derivativeJets.apply_const w).mul (hf.derivativeJets.apply_const w)
    convert H using 1
    · norm_num
      ring
    · funext y
      dsimp only [ψ]
      ring
  have hδ : QBoundedJets 2 (8*B*spatialStepDifferenceCoefficient 2 B*chainEnergy tail*‖w‖^2) δ :=
    qBoundedJets_chain_gradient_sq_sub tail ht hmT hvT w
  have hsq := abs_chain_gradient_sq_firstOrder_le tail ht hmT hvT w x
  have hout := abs_vectorIncrementAverage_firstOrder_le front hfront hψ hmF hvF x
  have hcomp := abs_pathGeneratorSum_sub_potential_le hf hF
    (qBoundedJets_chain_sub (p::tail) hinner hmI hvI) hψ front hmF x
  have hweak := abs_vectorIncrementAverage_sub_le front hfront hδ hmF (fun q hq => (hvF q hq).1) x
  have hψ2 := hψ.of_le (by norm_num : 2≤4)
  have hadd : vectorIncrementAverage front F (fun y => (fderiv ℝ T y w)^2) x =
      vectorIncrementAverage front F ψ x+vectorIncrementAverage front F δ x := by
    have he : (fun y => (fderiv ℝ T y w)^2) = fun y => ψ y+δ y := by
      funext y
      dsimp only [δ]
      ring
    rw [he]
    exact congrFun (vectorIncrementAverage_add front (hF.boundedDerivs (by norm_num))
      hψ.smooth.continuous hδ.smooth.continuous
      ((qBoundedJets_iff_qBddSmooth.mp hψ2).potential.boundedDerivs (by norm_num)).hasExpGrowth
      ((qBoundedJets_iff_qBddSmooth.mp hδ).potential.boundedDerivs (by norm_num)).hasExpGrowth) x
  have he : vectorIncrementAverage front F (fun y => (fderiv ℝ T y w)^2) x-
      firstOrderPathEnergy front tail f w x =
      ((fderiv ℝ T x w)^2-ψ x-
        2*fderiv ℝ f x w*pathGeneratorSum f (fun y => fderiv ℝ f y w) tail x)+
      (vectorIncrementAverage front F ψ x-ψ x-pathGeneratorSum F ψ front x)+
      (pathGeneratorSum F ψ front x-pathGeneratorSum f ψ front x)+
      (vectorIncrementAverage front F δ x-δ x) := by
    rw [hadd]
    dsimp only [firstOrderPathEnergy,ψ,δ]
    ring
  change |vectorIncrementAverage front F (fun y => (fderiv ℝ T y w)^2) x-
    firstOrderPathEnergy front tail f w x| ≤ _
  rw [he]
  calc
    _ ≤ |(fderiv ℝ T x w)^2-ψ x-
          2*fderiv ℝ f x w*pathGeneratorSum f (fun y => fderiv ℝ f y w) tail x|+
        |vectorIncrementAverage front F ψ x-ψ x-pathGeneratorSum F ψ front x|+
        |pathGeneratorSum F ψ front x-pathGeneratorSum f ψ front x|+
        |vectorIncrementAverage front F δ x-δ x| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hsq hout) hcomp) hweak

def pathEnergyValueCoefficient (B : ℝ) : ℝ :=
  (spatialStepDifferenceCoefficient 2 B)^2+18*B^2*pathValueExpansionCoefficient B+
    16*B^2*spatialStepDifferenceCoefficient 2 B+
    8*B*spatialStepDifferenceCoefficient 2 B*(1+B)^2

theorem pathEnergyValueCoefficient_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ pathEnergyValueCoefficient B := by
  have hK := spatialStepDifferenceCoefficient_nonneg 2 hB
  have hP := pathValueExpansionCoefficient_nonneg hB
  unfold pathEnergyValueCoefficient
  positivity

theorem abs_pathEnergy_firstOrder_total_le {B : ℝ} {f : E → ℝ}
    (front tail : List (ℝ × E)) (p : ℝ × E)
    (hinner : SpatialChainJets 5 B (p::tail) f)
    (hfront : SpatialChainJets 5 B front (vectorIncrementChain (p::tail) f))
    (hmI : ∀ q ∈ p::tail, q.1 ∈ Icc (0:ℝ) 1)
    (hvI : ∀ q ∈ p::tail, ‖q.2‖ ≤ 1 ∧ q.1*(B*‖q.2‖^2) ≤ 1/2)
    (hmF : ∀ q ∈ front, q.1 ∈ Icc (0:ℝ) 1)
    (hvF : ∀ q ∈ front, ‖q.2‖ ≤ 1 ∧ q.1*(B*‖q.2‖^2) ≤ 1/2) (w x : E) :
    |vectorIncrementAverage front (vectorIncrementChain (p::tail) f)
        (fun y => (fderiv ℝ (vectorIncrementChain tail f) y w)^2) x-
      firstOrderPathEnergy front tail f w x| ≤
      pathEnergyValueCoefficient B*‖w‖^2*(chainEnergy front+chainEnergy (p::tail))^2 := by
  have H := abs_pathEnergy_firstOrder_le front tail p hinner hfront hmI hvI hmF hvF w x
  have hB : 0 ≤ B := (hinner 0).nonneg
  have hK := spatialStepDifferenceCoefficient_nonneg 2 hB
  have hP := pathValueExpansionCoefficient_nonneg hB
  let E₀ := chainEnergy front+chainEnergy (p::tail)
  have hEf : 0 ≤ chainEnergy front := chainEnergy_nonneg _
  have hEt : 0 ≤ chainEnergy tail := chainEnergy_nonneg _
  have hEi : 0 ≤ chainEnergy (p::tail) := chainEnergy_nonneg _
  have hfE : chainEnergy front ≤ E₀ := le_add_of_nonneg_right hEi
  have hiE : chainEnergy (p::tail) ≤ E₀ := le_add_of_nonneg_left hEf
  have hti : chainEnergy tail ≤ chainEnergy (p::tail) := by
    rw [chainEnergy_cons]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have htE : chainEnergy tail ≤ E₀ := hti.trans hiE
  have hEt₂ : (chainEnergy tail)^2 ≤ E₀^2 := pow_le_pow_left₀ hEt htE 2
  have hEf₂ : (chainEnergy front)^2 ≤ E₀^2 := pow_le_pow_left₀ hEf hfE 2
  have hEiEf : chainEnergy (p::tail)*chainEnergy front ≤ E₀^2 := by
    simpa only [pow_two] using mul_le_mul hiE hfE hEf (hEf.trans hfE)
  have hEtEf : chainEnergy tail*chainEnergy front ≤ E₀^2 := by
    simpa only [pow_two] using mul_le_mul htE hfE hEf (hEt.trans htE)
  apply H.trans
  calc
    _ = ((spatialStepDifferenceCoefficient 2 B)^2+2*B^2*pathValueExpansionCoefficient B)*‖w‖^2*(chainEnergy tail)^2+
        (16*B^2*pathValueExpansionCoefficient B)*‖w‖^2*(chainEnergy front)^2+
        (16*B^2*spatialStepDifferenceCoefficient 2 B)*‖w‖^2*(chainEnergy (p::tail)*chainEnergy front)+
        (8*B*spatialStepDifferenceCoefficient 2 B*(1+B)^2)*‖w‖^2*(chainEnergy tail*chainEnergy front) := by ring
    _ ≤ ((spatialStepDifferenceCoefficient 2 B)^2+2*B^2*pathValueExpansionCoefficient B)*‖w‖^2*E₀^2+
        (16*B^2*pathValueExpansionCoefficient B)*‖w‖^2*E₀^2+
        (16*B^2*spatialStepDifferenceCoefficient 2 B)*‖w‖^2*E₀^2+
        (8*B*spatialStepDifferenceCoefficient 2 B*(1+B)^2)*‖w‖^2*E₀^2 := by gcongr
    _ = _ := by unfold pathEnergyValueCoefficient; ring

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner
open SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

def separableDirectional (φ : ℝ → ℝ) (j : ℕ) (c : E) (x : E) : ℝ :=
  ∑ i, c i*iteratedDeriv j φ (x i)

theorem fderiv_separableDirectional {φ : ℝ → ℝ} (hφ : ContDiff ℝ 5 φ)
    {j : ℕ} (hj : j < 5) (c v x : E) :
    fderiv ℝ (separableDirectional φ j c) x v =
      separableDirectional φ (j+1) (c*v) x := by
  have hd (i : Fin 3) : HasDerivAt (iteratedDeriv j φ) (iteratedDeriv (j+1) φ (x i)) (x i) := by
    rw [iteratedDeriv_succ]
    exact (hφ.differentiable_iteratedDeriv j (by exact_mod_cast hj) (x i)).hasDerivAt
  have hsum : HasFDerivAt (separableDirectional φ j c)
      (∑ i : Fin 3, (c i*iteratedDeriv (j+1) φ (x i)) • tripleCoordinate i) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    simpa only [Function.comp_def,tripleCoordinate_apply,smul_smul,smul_eq_mul] using
      ((hd i).comp_hasFDerivAt x (tripleCoordinate i).hasFDerivAt).const_mul (c i)
  rw [hsum.fderiv]
  simp only [separableDirectional,sum_apply,smul_apply,
    smul_eq_mul,Pi.mul_apply,tripleCoordinate_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem differentiable_separableDirectional {φ : ℝ → ℝ} (hφ : ContDiff ℝ 5 φ)
    {j : ℕ} (hj : j < 5) (c : E) : Differentiable ℝ (separableDirectional φ j c) := by
  have hd := hφ.differentiable_iteratedDeriv j (by exact_mod_cast hj)
  unfold separableDirectional
  apply Differentiable.fun_sum
  intro i _
  exact (hd.comp (tripleCoordinate i).differentiable).const_mul (c i)

private theorem separableDirectional_diagonal (φ : ℝ → ℝ) (j : ℕ) (c : E) (z : ℝ) :
    separableDirectional φ j c (fun _ => z) = iteratedDeriv j φ z*(∑ i, c i) := by
  simp only [separableDirectional,← Finset.sum_mul]
  ring

private theorem directionalJet_two_separable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 5 φ)
    {j : ℕ} (hj : j+1 < 5) (c v x : E) :
    directionalJet v 2 (separableDirectional φ j c) x =
      separableDirectional φ (j+2) ((c*v)*v) x := by
  have he : (fun y => fderiv ℝ (separableDirectional φ j c) y v) =
      separableDirectional φ (j+1) (c*v) :=
    funext (fun y => fderiv_separableDirectional hφ (by omega) c v y)
  change fderiv ℝ (fun y => fderiv ℝ (separableDirectional φ j c) y v) x v = _
  rw [he,fderiv_separableDirectional hφ hj]

theorem directionalJet_squared_separable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 5 φ)
    (w v x : E) :
    fderiv ℝ (fun y => (separableDirectional φ 1 w y)^2) x v =
      2*separableDirectional φ 1 w x*separableDirectional φ 2 (w*v) x ∧
    directionalJet v 2 (fun y => (separableDirectional φ 1 w y)^2) x =
      2*(separableDirectional φ 2 (w*v) x)^2+
        2*separableDirectional φ 1 w x*separableDirectional φ 3 ((w*v)*v) x := by
  have hd₁ := differentiable_separableDirectional hφ (by norm_num : 1<5) w
  have hd₂ := differentiable_separableDirectional hφ (by norm_num : 2<5) (w*v)
  have hfirst (y : E) : fderiv ℝ (fun z => (separableDirectional φ 1 w z)^2) y v =
      2*(separableDirectional φ 1 w y*separableDirectional φ 2 (w*v) y) := by
    rw [fderiv_fun_pow 2 (hd₁ y)]
    simp only [Nat.reduceSub,pow_one,smul_apply,smul_eq_mul]
    rw [fderiv_separableDirectional hφ (by norm_num)]
    ring
  refine ⟨by rw [hfirst]; ring,?_⟩
  change fderiv ℝ (fun y => fderiv ℝ (fun z => (separableDirectional φ 1 w z)^2) y v) x v = _
  simp_rw [hfirst]
  change (fderiv ℝ (fun y => 2*((separableDirectional φ 1 w*separableDirectional φ 2 (w*v)) y)) x) v = _
  rw [fderiv_const_mul (hd₁.mul hd₂ x) 2,fderiv_mul (hd₁ x) (hd₂ x)]
  simp only [smul_apply,smul_eq_mul,add_apply]
  rw [fderiv_separableDirectional hφ (by norm_num),fderiv_separableDirectional hφ (by norm_num)]
  ring

theorem pathGenerator_separable_diagonal {φ : ℝ → ℝ} (hφ : ContDiff ℝ 5 φ)
    (m : ℝ) (w v : E) (z : ℝ) :
    let G := separableDirectional φ 0 (fun _ => 1)
    pathGenerator m v G (separableDirectional φ 1 w) (fun _ => z) =
      m*(iteratedDeriv 1 φ z)*(iteratedDeriv 2 φ z)*(∑ i, v i)*(∑ i, w i*v i)+
      (iteratedDeriv 3 φ z)*(∑ i, w i*v i^2)/2 := by
  dsimp only
  rw [pathGenerator,fderiv_separableDirectional hφ (by norm_num),
    fderiv_separableDirectional hφ (by norm_num),directionalJet_two_separable hφ (by norm_num)]
  simp only [separableDirectional_diagonal,Pi.mul_apply,one_mul]
  congr 1
  · ring
  · congr 1
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private theorem separable_gradient {φ : ℝ → ℝ} (hφ : ContDiff ℝ 5 φ) (w : E) :
    (fun x => fderiv ℝ (separableDirectional φ 0 (fun _ => 1)) x w) =
      separableDirectional φ 1 w := by
  funext x
  rw [fderiv_separableDirectional hφ (by norm_num)]
  congr 1
  funext i
  exact one_mul (w i)

private theorem pathGenerator_squared_separable_diagonal {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 5 φ) (m : ℝ) (w v : E) (z : ℝ) :
    let u := iteratedDeriv 1 φ z
    let chi := iteratedDeriv 2 φ z
    let d := iteratedDeriv 3 φ z
    let G := separableDirectional φ 0 (fun _ => 1)
    pathGenerator m v G (fun x => (separableDirectional φ 1 w x)^2) (fun _ => z) =
      2*m*u^2*chi*(∑ i, v i)*(∑ i, w i)*(∑ i, w i*v i)+
        chi^2*(∑ i, w i*v i)^2+u*d*(∑ i, w i)*(∑ i, w i*v i^2) := by
  dsimp only
  rw [pathGenerator,fderiv_separableDirectional hφ (by norm_num),
    (directionalJet_squared_separable hφ w v _).1,
    (directionalJet_squared_separable hφ w v _).2]
  simp only [separableDirectional_diagonal,Pi.mul_apply,one_mul]
  have he : (∑ i, w i*v i*v i) = ∑ i, w i*v i^2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

private theorem list_sum_take_eq_fin {A Y : Type*} [AddCommMonoid Y]
    (l : List A) (n : ℕ) (g : A → Y) :
    ((l.take n).map g).sum = ∑ i : Fin l.length, if i.val < n then g (l.get i) else 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons]
    cases n with
    | zero => simp
    | succ n =>
      rw [List.take_succ_cons,List.map_cons,List.sum_cons,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,Nat.zero_lt_succ,ite_true,List.getElem_cons_zero,
        Fin.val_succ,Nat.succ_lt_succ_iff,List.get_eq_getElem,List.getElem_cons_succ]

private theorem list_sum_drop_succ_eq_fin {A Y : Type*} [AddCommMonoid Y]
    (l : List A) (n : ℕ) (g : A → Y) :
    ((l.drop (n+1)).map g).sum = ∑ i : Fin l.length, if n < i.val then g (l.get i) else 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons]
    cases n with
    | zero =>
      rw [List.drop_succ_cons,Fin.sum_univ_succ]
      simp only [List.drop_zero,Fin.val_zero,lt_self_iff_false,ite_false,Fin.val_succ,
        Nat.zero_lt_succ,ite_true,zero_add,List.get_eq_getElem,List.getElem_cons_succ]
      have he : l.map g = List.ofFn (fun i : Fin l.length => g (l.get i)) := by
        simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map l g).symm
      rw [he,List.sum_ofFn]
      simp only [List.get_eq_getElem]
    | succ n =>
      rw [List.drop_succ_cons,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,Nat.not_lt_zero,ite_false,zero_add,Fin.val_succ,
        Nat.succ_lt_succ_iff,List.get_eq_getElem,List.getElem_cons_succ]

theorem firstOrderPathEnergy_separable_eq_polynomial {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 5 φ) (l : List (ℝ × E)) (j : Fin l.length) (z : ℝ) :
    firstOrderPathEnergy (l.take j.val) (l.drop (j.val+1))
      (separableDirectional φ 0 (fun _ => 1)) (l.get j).2 (fun _ => z) =
      firstOrderPathPolynomial 1 (iteratedDeriv 1 φ z) (iteratedDeriv 2 φ z)
        (iteratedDeriv 3 φ z) (fun i => (l.get i).1) (fun i => (l.get i).2) j := by
  let u := iteratedDeriv 1 φ z
  let chi := iteratedDeriv 2 φ z
  let d := iteratedDeriv 3 φ z
  let w := (l.get j).2
  let inner := fun q : ℝ × E =>
    q.1*u*chi*(∑ i, q.2 i)*(∑ i, w i*q.2 i)+d*(∑ i, w i*(q.2 i)^2)/2
  let outer := fun q : ℝ × E =>
    2*q.1*u^2*chi*(∑ i, q.2 i)*(∑ i, w i)*(∑ i, w i*q.2 i)+
      chi^2*(∑ i, w i*q.2 i)^2+u*d*(∑ i, w i)*(∑ i, w i*(q.2 i)^2)
  have hI (t : List (ℝ × E)) : pathGeneratorSum (separableDirectional φ 0 (fun _ => 1))
      (separableDirectional φ 1 w) t (fun _ => z) = (t.map inner).sum := by
    induction t with
    | nil => rfl
    | cons q t ih =>
      rw [pathGeneratorSum,pathGenerator_separable_diagonal hφ,ih]
      rfl
  have hO (t : List (ℝ × E)) : pathGeneratorSum (separableDirectional φ 0 (fun _ => 1))
      (fun x => (separableDirectional φ 1 w x)^2) t (fun _ => z) = (t.map outer).sum := by
    induction t with
    | nil => rfl
    | cons q t ih =>
      rw [pathGeneratorSum,pathGenerator_squared_separable_diagonal hφ,ih]
      rfl
  rw [firstOrderPathEnergy]
  have hgrad (x : E) : fderiv ℝ (separableDirectional φ 0 (fun _ => 1)) x (l.get j).2 =
      separableDirectional φ 1 w x := congrFun (separable_gradient hφ (l.get j).2) x
  simp_rw [hgrad]
  rw [separableDirectional_diagonal,hI,hO,list_sum_drop_succ_eq_fin,list_sum_take_eq_fin]
  change (u*pathCoordinateSum w)^2+2*(u*pathCoordinateSum w)*
    (∑ i : Fin l.length, if j.val < i.val then inner (l.get i) else 0)+
    (∑ i : Fin l.length, if i.val < j.val then outer (l.get i) else 0) = _
  unfold firstOrderPathPolynomial
  simp only [one_pow,one_mul]
  have distribute (c : ℝ) (F : Fin l.length → ℝ) : c*(∑ i, F i) = ∑ i, c*F i :=
    Finset.mul_sum _ _ _
  rw [distribute,distribute,distribute,distribute]
  simp only [add_assoc,← Finset.sum_add_distrib]
  have hbase : (u*pathCoordinateSum w)^2 =
      (iteratedDeriv 1 φ z)^2*(pathCoordinateSum (l.get j).2)^2 := by
    dsimp only [u,w]
    ring
  rw [hbase]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hdot : (∑ a, (l.get j).2 a*(l.get i).2 a) = ∑ a, (l.get i).2 a*(l.get j).2 a := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hcube : (∑ a, (l.get j).2 a*((l.get i).2 a)^2) =
      ∑ a, ((l.get i).2 a)^2*(l.get j).2 a := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  by_cases hij : i=j
  · subst i
    simp only [lt_self_iff_false,ite_false,ite_true]
    ring
  · have hv : i.val≠j.val := fun H => hij (Fin.ext H)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · simp only [Fin.lt_def,hlt,Nat.not_lt.mpr hlt.le,ite_true,ite_false,hij]
      dsimp only [inner,outer,u,chi,d,w,pathCoordinateSum,pathDot]
      rw [hdot,hcube]
      ring
    · simp only [Fin.lt_def,hgt,Nat.not_lt.mpr hgt.le,ite_true,ite_false,hij]
      dsimp only [inner,outer,u,chi,d,w,pathCoordinateSum,pathDot]
      rw [hdot,hcube]
      ring

private theorem firstOrderPathPolynomial_cast {n t : ℕ} (hn : n=t) (b u chi d : ℝ)
    (m : Fin t → ℝ) (v : Fin t → E) (j : Fin n) :
    firstOrderPathPolynomial b u chi d (fun i => m (Fin.cast hn i)) (fun i => v (Fin.cast hn i)) j =
      firstOrderPathPolynomial b u chi d m v (Fin.cast hn j) := by
  subst t
  rfl

private theorem firstOrderPathEnergy_ofFn_eq_polynomial {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 5 φ) {n : ℕ} (m : Fin n → ℝ) (v : Fin n → E) (j : Fin n) (z : ℝ) :
    let l := List.ofFn (fun i => (m i,v i))
    firstOrderPathEnergy (l.take j.val) (l.drop (j.val+1))
      (separableDirectional φ 0 (fun _ => 1)) (v j) (fun _ => z) =
      firstOrderPathPolynomial 1 (iteratedDeriv 1 φ z) (iteratedDeriv 2 φ z)
        (iteratedDeriv 3 φ z) m v j := by
  let l := List.ofFn (fun i => (m i,v i))
  have hn : l.length=n := List.length_ofFn
  have H := firstOrderPathEnergy_separable_eq_polynomial hφ l (Fin.cast hn.symm j) z
  have hm : (fun i : Fin l.length => (l.get i).1) = fun i => m (Fin.cast hn i) := by
    funext i
    simp only [l,List.get_eq_getElem,List.getElem_ofFn]
    exact congrArg m (Fin.ext rfl)
  have hv : (fun i : Fin l.length => (l.get i).2) = fun i => v (Fin.cast hn i) := by
    funext i
    simp only [l,List.get_eq_getElem,List.getElem_ofFn]
    exact congrArg v (Fin.ext rfl)
  rw [hm,hv,firstOrderPathPolynomial_cast] at H
  simpa only [l,Fin.val_cast,List.get_eq_getElem,List.getElem_ofFn,Fin.cast_cast,Fin.cast_eq_self] using H

private theorem firstOrderPathPolynomial_smul {n : ℕ} (β u chi d : ℝ)
    (m : Fin n → ℝ) (v : Fin n → E) (j : Fin n) :
    firstOrderPathPolynomial 1 u chi d m (fun i => β • v i) j =
      firstOrderPathPolynomial (β^2) u chi d m v j := by
  have hs (w : E) : pathCoordinateSum (β • w) = β*pathCoordinateSum w := by
    simp only [pathCoordinateSum,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  have hd (v w : E) : pathDot (β • v) (β • w) = β^2*pathDot v w := by
    unfold pathDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  have ht (i : Fin n) : (∑ a, ((β • v i) a)^2*(β • v j) a) =
      β^3*(∑ a, (v i a)^2*v j a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  have scale₁ (c : ℝ) (F : Fin n → ℝ) :
      (∑ i, if i=j then 0 else c*F i) = c*(∑ i, if i=j then 0 else F i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [mul_zero]
  have scale₂ (c : ℝ) (F : Fin n → ℝ) :
      (∑ i, if i<j then c*F i else 0) = c*(∑ i, if i<j then F i else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [mul_zero]
  have hm : (∑ i, if i=j then 0 else m i*pathCoordinateSum (β • v i)*pathDot (β • v i) (β • v j)) =
      β^3*(∑ i, if i=j then 0 else m i*pathCoordinateSum (v i)*pathDot (v i) (v j)) := by
    rw [← scale₁]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · rfl
    · rw [hs,hd]
      ring
  have hp : (∑ i, if i<j then (pathDot (β • v i) (β • v j))^2 else 0) =
      β^4*(∑ i, if i<j then (pathDot (v i) (v j))^2 else 0) := by
    rw [← scale₂]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · rw [hd]
      ring
    · rfl
  unfold firstOrderPathPolynomial
  rw [hm,hp]
  simp only [hs,ht,scale₁,one_pow,one_mul]
  ring

def windowEntryMass (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) (lam : ℝ)
    (j : Fin (windowMassPath β α a p s h k N).length) : ℝ :=
  ((windowMassPath β α a p s h k N).get j).1+
    lam*((windowMassPath β α a p s h k N).get j).2.1

private theorem window_entry_direction (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ)
    (j : Fin (windowMassPath β α a p s h k N).length) :
    ((windowMassPath β α a p s h k N).get j).2.2 =
      β • windowRawDirection β α a p s h k N j := by
  rw [List.get_eq_getElem]
  unfold windowRawDirection
  rw [List.get_eq_getElem]
  simp only [windowMassPath,List.getElem_map]

private theorem massPath_window_ofFn (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ)
    (N : ℕ) (lam : ℝ) :
    massPath (windowMassPath β α a p s h k N) lam = List.ofFn
      (fun j => (windowEntryMass β α a p s h k N lam j,
        β • windowRawDirection β α a p s h k N j)) := by
  conv_lhs =>
    arg 1
    rw [← List.ofFn_get (windowMassPath β α a p s h k N)]
  simp only [massPath,List.map_ofFn,Function.comp_def,windowEntryMass,window_entry_direction]

private theorem interpolated_window_ofFn (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ)
    (N : ℕ) (lam : ℝ) :
    OW.window (interpolatedProfile α a lam) p s h k N = List.ofFn
      (fun j : Fin (windowMassPath β α a p s h k N).length =>
        (windowEntryMass β α a p s h k N lam j,windowRawDirection β α a p s h k N j)) := by
  rw [window_eq_massSamples,← List.ofFn_getElem_eq_map]
  simp only [windowEntryMass,windowMassPath,windowRawDirection,List.length_map,
    List.get_eq_getElem,List.getElem_map]
  congr 1
  funext j
  congr 1
  simp only [Fin.val_cast]
  unfold interpolatedProfile
  ring

private theorem covariance_ofFn {n : ℕ} (m : Fin n → ℝ) (v : Fin n → E) :
    matrixChainCovariance (List.ofFn (fun i => (m i,v i))) = ∑ i, rankOneMatrix (v i) := by
  have he (l : List (ℝ × E)) : matrixChainCovariance l = (l.map (fun q => rankOneMatrix q.2)).sum := by
    induction l with
    | nil => rfl
    | cons q l ih => simp only [matrixChainCovariance_cons,List.map_cons,List.sum_cons,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

private theorem window_raw_diagonal (β : ℝ) (α : ℝ → ℝ) (a p s h k lam : ℝ)
    {N : ℕ} (hN : 0<N) (hh : 0≤h) (hp : p ∈ Icc (0:ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2) :
    ∀ b : Fin 3, (∑ j, (windowRawDirection β α a p s h k N j b)^2) = 4*h := by
  have H := window_covariance (interpolatedProfile α a lam) p s h k hN hh hp hl
  rw [interpolated_window_ofFn β α a p s h k N lam,covariance_ofFn] at H
  intro b
  have Hb := congrFun (congrFun H b) b
  simp only [Finset.sum_apply,rankOneMatrix] at Hb
  rw [show (∑ j, windowRawDirection β α a p s h k N j b*
      windowRawDirection β α a p s h k N j b) =
      ∑ j, (windowRawDirection β α a p s h k N j b)^2 by
        apply Finset.sum_congr rfl; intro j _; ring] at Hb
  fin_cases b <;> simpa [mul_comm] using Hb

private theorem translation_ofFn {n : ℕ} (m : Fin n → ℝ) (v : Fin n → E) :
    translation (List.ofFn (fun i => (m i,v i))) = ∑ i, m i • (pathCoordinateSum (v i) • v i) := by
  simp only [translation,List.map_ofFn,List.sum_ofFn,Function.comp_def,pathCoordinateSum]

theorem firstOrderPathEnergy_window_eq (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ)
    {N : ℕ} (hN : 0<N) (hh : 0≤h) (hp : p ∈ Icc (0:ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2) (lam z : ℝ)
    (hφ : ContDiff ℝ 5 (Phi β α (s+4*h)))
    (j : Fin (windowMassPath β α a p s h k N).length) :
    let l := massPath (windowMassPath β α a p s h k N) lam
    firstOrderPathEnergy (l.take j.val) (l.drop (j.val+1)) (massVariationTerminal β α s h)
      ((windowMassPath β α a p s h k N).get j).2.2 (fun _ => z) =
      β^2*windowMassEnergyEntry β α a p s h k N lam j z-
        pathEnergySelfInteraction (β^2) (jet β α 1 (s+4*h) z) (jet β α 2 (s+4*h) z)
          (jet β α 3 (s+4*h) z) (windowEntryMass β α a p s h k N lam j)
          (windowRawDirection β α a p s h k N j) := by
  dsimp only
  have hterm : massVariationTerminal β α s h =
      separableDirectional (Phi β α (s+4*h)) 0 (fun _ => 1) := by
    funext x
    simp only [massVariationTerminal,separableDirectional,iteratedDeriv_zero,one_mul]
  rw [hterm,massPath_window_ofFn,window_entry_direction,
    firstOrderPathEnergy_ofFn_eq_polynomial hφ,firstOrderPathPolynomial_smul,
    firstOrderPathPolynomial_eq_energy (β^2) _ _ _ h _ _ j
      (window_raw_diagonal β α a p s h k lam hN hh hp hl)]
  rw [← translation_ofFn,← interpolated_window_ofFn β α a p s h k N lam]
  rfl

private theorem coordinate_power_sum_le (v : E) (n : ℕ) :
    |∑ i, (v i)^n| ≤ 3*‖v‖^n := by
  calc
    _ ≤ ∑ i, |(v i)^n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ‖v‖^n := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) n
    _ = _ := by simp

private theorem pathEnergySelfInteraction_smul (β u chi d m : ℝ) (v : E) :
    pathEnergySelfInteraction (β^2) u chi d m v =
      pathEnergySelfInteraction 1 u chi d m (β • v) := by
  simp only [pathEnergySelfInteraction,pathCoordinateSum,Pi.smul_apply,smul_eq_mul,mul_pow,
    ← Finset.mul_sum,one_pow,one_mul]

  ring

theorem abs_pathEnergySelfInteraction_le {T u chi d m : ℝ}
    (hT : 0≤T) (hu : |u|≤T) (hc : |chi|≤T) (hd : |d|≤T)
    (hm : m ∈ Icc (0:ℝ) 1) (v : E) :
    |pathEnergySelfInteraction 1 u chi d m v| ≤ (9*T^2+54*T^3)*‖v‖^4 := by
  have h₁ : |pathCoordinateSum v| ≤ 3*‖v‖ := by
    simpa only [pow_one,pathCoordinateSum] using coordinate_power_sum_le v 1
  have h₂ := coordinate_power_sum_le v 2
  have h₃ := coordinate_power_sum_le v 3
  unfold pathEnergySelfInteraction
  simp only [one_pow,one_mul]
  calc
    _ ≤ |u*d*pathCoordinateSum v*(∑ a, (v a)^3)| +
        |2*m*u^2*chi*(pathCoordinateSum v)^2*(∑ a, (v a)^2)| := abs_add_le _ _
    _ ≤ T*T*(3*‖v‖)*(3*‖v‖^3)+2*1*T^2*T*(3*‖v‖)^2*(3*‖v‖^2) := by
      simp only [abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg hm.1]
      gcongr
      exact hm.2
    _ = _ := by ring

end SKBarriers2.Corner

namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem SpatialChainJets.drop {r : ℕ} {B : ℝ} {l : List (ℝ × E)} {f : E → ℝ}
    (hjets : SpatialChainJets r B l f) (j : ℕ) : SpatialChainJets r B (l.drop j) f := by
  intro n
  simpa only [List.drop_drop] using hjets (j+n)

theorem SpatialChainJets.prefix {r : ℕ} {B : ℝ} {l : List (ℝ × E)} {f : E → ℝ}
    (hjets : SpatialChainJets r B l f) (j : ℕ) :
    SpatialChainJets r B (l.take j) (vectorIncrementChain (l.drop j) f) := by
  intro n
  rw [← vectorIncrementChain_append]
  by_cases hnj : n≤j
  · rw [List.drop_take]
    have he : (l.drop n).take (j-n)++l.drop j=l.drop n := by
      simpa only [Nat.add_sub_of_le hnj] using List.drop_take_append_drop l n (j-n)
    rw [he]
    exact hjets n
  · have hjn : j≤n := by omega
    have he : (l.take j).drop n=[] := List.drop_eq_nil_iff.mpr
      ((List.length_take_le j l).trans hjn)
    rw [he,List.nil_append]
    exact hjets j

theorem SpatialChainJets.of_inner {B δ : ℝ} {l : List (ℝ × E)} {f : E → ℝ}
    (hinner : ∀ n, QPotential 5 B (vectorIncrementChain (l.drop (n+1)) f))
    (hm : ∀ q ∈ l, q.1 ∈ Icc (0:ℝ) 1)
    (hv : ∀ q ∈ l, ‖q.2‖^2 ≤ δ ∧ q.1*(B*‖q.2‖^2) ≤ 1/2)
    (hδ : stepStabilityCoefficient 5 B*δ ≤ 1) : SpatialChainJets 5 (B+1) l f := by
  have hB : 0≤B := (hinner 0).nonneg
  intro n
  cases n with
  | succ n => exact (hinner n).mono (by linarith)
  | zero =>
    simp only [List.drop_zero]
    cases l with
    | nil => simpa only [List.drop_nil,vectorIncrementChain] using (hinner 0).mono (by linarith)
    | cons q t =>
      have ht : QPotential 5 B (vectorIncrementChain t f) := by
        simpa only [List.drop_succ_cons,List.drop_zero] using hinner 0
      have H := qPotential_step ht (by norm_num) (hm q (by simp)) q.2 (hv q (by simp)).2
      apply H.mono
      have hK := stepStabilityCoefficient_nonneg 5 hB
      have hq := mul_le_mul_of_nonneg_left (hv q (by simp)).1 hK
      linarith

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner
open SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem windowGradientEnergy_firstOrder_le (β : ℝ) (α : ℝ → ℝ) (a p s h k lam B : ℝ)
    {N : ℕ} (hN : 0<N) (hh : 0≤h) (hp : p ∈ Icc (0:ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2)
    (hφ : ContDiff ℝ 5 (Phi β α (s+4*h)))
    (hjets : SpatialChainJets 5 B (massPath (windowMassPath β α a p s h k N) lam)
      (massVariationTerminal β α s h))
    (hm : ∀ q ∈ massPath (windowMassPath β α a p s h k N) lam, q.1 ∈ Icc (0:ℝ) 1)
    (hv : ∀ q ∈ massPath (windowMassPath β α a p s h k N) lam,
      ‖q.2‖≤1 ∧ q.1*(B*‖q.2‖^2)≤1/2)
    (j : Fin (windowMassPath β α a p s h k N).length) (z : ℝ) :
    |windowGradientEnergy β α a p s h k N lam j z-
      (β^2*windowMassEnergyEntry β α a p s h k N lam j z-
        pathEnergySelfInteraction (β^2) (jet β α 1 (s+4*h) z) (jet β α 2 (s+4*h) z)
          (jet β α 3 (s+4*h) z) (windowEntryMass β α a p s h k N lam j)
          (windowRawDirection β α a p s h k N j))| ≤
      pathEnergyValueCoefficient B*‖((windowMassPath β α a p s h k N).get j).2.2‖^2*
        (chainEnergy (massPath (windowMassPath β α a p s h k N) lam))^2 := by
  let l := massPath (windowMassPath β α a p s h k N) lam
  let jj : Fin l.length := ⟨j.val,by simpa only [l,massPath,List.length_map] using j.isLt⟩
  have hrest : l.drop j.val=l.get jj::l.drop (j.val+1) := List.drop_eq_getElem_cons jj.isLt
  have hI : SpatialChainJets 5 B (l.get jj::l.drop (j.val+1)) (massVariationTerminal β α s h) := by
    rw [← hrest]
    exact hjets.drop j.val
  have hF : SpatialChainJets 5 B (l.take j.val)
      (vectorIncrementChain (l.get jj::l.drop (j.val+1)) (massVariationTerminal β α s h)) := by
    rw [← hrest]
    exact hjets.prefix j.val
  have hmem (q : ℝ × E) (hq : q ∈ l.get jj::l.drop (j.val+1)) : q ∈ l := by
    rw [← hrest] at hq
    exact List.mem_of_mem_drop hq
  have H := abs_pathEnergy_firstOrder_total_le (l.take j.val) (l.drop (j.val+1)) (l.get jj)
    hI hF (fun q hq => hm q (hmem q hq)) (fun q hq => hv q (hmem q hq))
    (fun q hq => hm q (List.mem_of_mem_take hq)) (fun q hq => hv q (List.mem_of_mem_take hq))
    ((windowMassPath β α a p s h k N).get j).2.2 (fun _ => z)
  rw [← hrest] at H
  have he : chainEnergy (l.take j.val)+chainEnergy (l.drop j.val)=chainEnergy l := by
    rw [← chainEnergy_append,List.take_append_drop]
  rw [he,firstOrderPathEnergy_window_eq β α a p s h k hN hh hp hl lam z hφ j] at H
  simpa only [windowGradientEnergy,l,massPath,List.map_take,List.map_drop] using H

end SKBarriers2.Corner

namespace SKBarriers2.Corner
open SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem abs_halved_difference_le {A L S M T : ℝ}
    (hA : |A-(L-S)|≤M) (hS : |S|≤T) : |A/2-L/2|≤M/2+T/2 := by
  have he : A/2-L/2=(A-(L-S))/2-S/2 := by ring
  rw [he]
  calc
    _ ≤ |(A-(L-S))/2|+|S/2| := abs_sub _ _
    _ = |A-(L-S)|/2+|S|/2 := by rw [abs_div,abs_div]; norm_num
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hA (by norm_num))
      (div_le_div_of_nonneg_right hS (by norm_num))

private theorem energy_step_size_le {K D h n t e : ℝ}
    (hK : 0≤K) (hD : 0≤D) (hh : 0<h) (hh1 : h≤1) (hn : 0<n)
    (_ht : 0≤t) (he : 0≤e) (htb : t≤D*h/n) (heb : e≤12*D*h) :
    (K/2)*t*e^2≤(72*K*D^3)*(Real.sqrt h*h^2)/n := by
  have hsqrt : h≤Real.sqrt h := by
    have hsq : h*h≤h := mul_le_of_le_one_right hh.le hh1
    nlinarith only [hsq,Real.sq_sqrt hh.le,Real.sqrt_nonneg h,hh.le]
  have hcube : h^3≤Real.sqrt h*h^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hsqrt (sq_nonneg h)]
  calc
    _ ≤ (K/2)*(D*h/n)*(12*D*h)^2 := by gcongr
    _ = (72*K*D^3)*h^3/n := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by positivity)) hn.le

private theorem quartic_step_size_le {S D h n t eps : ℝ}
    (hS : 0≤S) (_hD : 0≤D) (_hh : 0≤h) (hn : 0<n) (ht : 0≤t)
    (htb : t≤D*h/n) (hsmall : S*D^2*h^2/n≤eps) :
    (S/2)*t^2≤(eps/2)/n := by
  calc
    _ ≤ (S/2)*(D*h/n)^2 := by gcongr
    _ = (S*D^2*h^2/n)/(2*n) := by field_simp
    _ ≤ eps/(2*n) := div_le_div_of_nonneg_right hsmall (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 600000 in
theorem scalarData_massSensitivityValueBound {β : ℝ} (D₀ : ScalarData β) {l u : ℝ}
    (hl : 0<l) (hu : u<D₀.q)
    (hA : UniformWindowEntropyInputs β (cdf (D₀.μ : Measure ℝ)) (Icc l u)) :
    MassSensitivityValueBound β (cdf (D₀.μ : Measure ℝ)) (Icc l u) := by
  let α := cdf (D₀.μ : Measure ℝ)
  obtain ⟨B,a0,D,hA0,kapA,hB,ha0,hD,hhA,hkapA,hA⟩ := hA
  obtain ⟨hE0,kapE,hhE,hkapE,hEntropy⟩ :=
    entropyPathRemainder_value_small_of_entropyInputs
      ⟨B,a0,D,hA0,kapA,hB,ha0,hD,hhA,hkapA,hA⟩
  let B₁ := B+1
  let K := pathEnergyValueCoefficient B₁
  let T := scalarTerminalJetBound D₀ 3
  let S := 9*T^2+54*T^3
  have hB₁ : 0<B₁ := by dsimp only [B₁]; linarith
  have hK : 0≤K := pathEnergyValueCoefficient_nonneg hB₁.le
  have hT : 0≤T := scalarTerminalJetBound_nonneg D₀ _
  have hS : 0≤S := by dsimp only [S]; positivity
  let h0 := min hA0 (min hE0 (min 1 (min (l/2) ((D₀.q-u)/6))))
  let kap := min kapA (min kapE (1/2))
  refine ⟨72*K*D^3,h0,kap,by positivity,
    lt_min hhA (lt_min hhE (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))),
    lt_min hkapA (lt_min hkapE (by norm_num)),?_⟩
  intro r hr h hh hh0 eps heps
  have hhA' : h≤hA0 := hh0.trans (min_le_left _ _)
  have hhE' : h≤hE0 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1 : h≤1 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhl : h≤l/2 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hhq : h≤(D₀.q-u)/6 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2,D₀.q_mem.2]
  have hφ : ContDiff ℝ 5 (Phi β α ((r-h)+4*h)) := (scalarData_phi_contDiff D₀ ht).of_le (by simp)
  have hjet (j : ℕ) (hj : 1≤j) (hj3 : j≤3) (z : ℝ) : |jet β α j ((r-h)+4*h) z|≤T :=
    scalarData_jet_le D₀ hj hj3 ht z
  have hδlim : Tendsto (fun N : ℕ => D*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hstepLim : Tendsto (fun N : ℕ => stepStabilityCoefficient 5 B*(D*h/(N:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hδlim.const_mul (stepStabilityCoefficient 5 B)
  have hselfLim : Tendsto (fun N : ℕ => S*D^2*h^2/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hδlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    hδlim.eventually (eventually_le_nhds (by positivity : (0:ℝ)<1/(2*B₁))),
    hstepLim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    hselfLim.eventually (eventually_le_nhds heps),
    hEntropy r hr h hh hhE' (eps/2) (by positivity)] with N hN hδ1 hδB hstep hself hEnt
  intro lam hlam z j k hk
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hkA : |k|≤kapA := hk.trans (min_le_left _ _)
  have hkE : |k|≤kapE := hk.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkhalf : |k|≤1/2 := hk.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hf,hAi⟩ := hA r hr h hh hhA' k hkA N hN
  obtain ⟨hinner,hentry⟩ := hAi lam hlam
  let L := windowMassPath β α (α (r-h)) (1/2) (r-h) h k N
  let ls := massPath L lam
  let f := massVariationTerminal β α (r-h) h
  let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
  let v := (L.get jj).2.2
  let δ := D*h/(N:ℝ)
  have hδ : 0≤δ := by positivity
  have hlen : L.length=12*N := windowMassPath_length _ _ _ _ _ _ _ _
  have hlenpos : 0<L.length := by rw [hlen]; omega
  have hlslen : ls.length=L.length := by simp only [ls,massPath,List.length_map]
  have hentries : ∀ q ∈ ls, q.1 ∈ Icc a0 1 ∧ ‖q.2‖^2≤δ := by
    intro q hq
    change q ∈ L.map (fun p => (p.1+lam*p.2.1,p.2.2)) at hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    rw [← hi]
    exact hentry i
  have hm : ∀ q ∈ ls, q.1 ∈ Icc (0:ℝ) 1 := by
    intro q hq
    exact ⟨ha0.le.trans (hentries q hq).1.1,(hentries q hq).1.2⟩
  have hv₁ : ∀ q ∈ ls, ‖q.2‖≤1 ∧ q.1*(B₁*‖q.2‖^2)≤1/2 := by
    intro q hq
    have hnorm := (hentries q hq).2
    refine ⟨by nlinarith [norm_nonneg q.2],?_⟩
    calc
      _ ≤ B₁*‖q.2‖^2 := mul_le_of_le_one_left (by positivity) (hm q hq).2
      _ ≤ B₁*δ := mul_le_mul_of_nonneg_left hnorm hB₁.le
      _ ≤ 1/2 := by
        have H := (le_div_iff₀ (by positivity : 0<2*B₁)).mp hδB
        linarith
  have hf5 : QPotential 5 B f := by
    have hlast : L.length-1<L.length := Nat.sub_lt hlenpos (by norm_num)
    have H := (hinner (L.length-1) hlast).of_le (by norm_num : 5≤10)
    have he : ls.drop (L.length-1+1)=[] := List.drop_eq_nil_iff.mpr (by rw [hlslen]; omega)
    change QPotential 5 B (vectorIncrementChain (ls.drop (L.length-1+1)) f) at H
    rw [he] at H
    exact H
  have hI : ∀ n, QPotential 5 B (vectorIncrementChain (ls.drop (n+1)) f) := by
    intro n
    by_cases hnL : n<L.length
    · exact (hinner n hnL).of_le (by norm_num)
    · rw [List.drop_eq_nil_iff.mpr (by rw [hlslen]; omega)]
      exact hf5
  have hjets : SpatialChainJets 5 B₁ ls f := SpatialChainJets.of_inner hI hm (by
    intro q hq
    refine ⟨(hentries q hq).2,?_⟩
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by dsimp only [B₁]; linarith : B≤B₁)
      (sq_nonneg ‖q.2‖)) (hm q hq).1).trans (hv₁ q hq).2) hstep
  have henergy : chainEnergy ls≤12*D*h := by
    have H := List.sum_le_length_nsmul (ls.map (fun q => ‖q.2‖^2)) δ (by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      exact (hentries q hq).2)
    change chainEnergy ls≤_ at H
    simp only [List.length_map,hlslen,hlen,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at H
    exact H.trans_eq (by dsimp only [δ]; field_simp)
  have hdir : ‖v‖^2≤δ := (hentry jj).2
  have hEn := windowGradientEnergy_firstOrder_le β α (α (r-h)) (1/2) (r-h) h k lam B₁
    hN hh.le (by norm_num) (OW.repairLength_mem (by norm_num) hkhalf) hφ hjets hm hv₁ jj z
  let si := pathEnergySelfInteraction (β^2) (jet β α 1 ((r-h)+4*h) z)
    (jet β α 2 ((r-h)+4*h) z) (jet β α 3 ((r-h)+4*h) z)
    (windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj)
    (windowRawDirection β α (α (r-h)) (1/2) (r-h) h k N jj)
  change |windowGradientEnergy β α (α (r-h)) (1/2) (r-h) h k N lam jj z-
    (β^2*windowMassEnergyEntry β α (α (r-h)) (1/2) (r-h) h k N lam jj z-si)| ≤
    K*‖v‖^2*(chainEnergy ls)^2 at hEn
  have hsi : |si|≤S*‖v‖^4 := by
    dsimp only [si]
    rw [pathEnergySelfInteraction_smul,← window_entry_direction]
    exact abs_pathEnergySelfInteraction_le hT (hjet 1 (by norm_num) (by norm_num) z)
      (hjet 2 (by norm_num) (by norm_num) z) (hjet 3 (by norm_num) (by norm_num) z)
      ⟨ha0.le.trans (hentry jj).1.1,(hentry jj).1.2⟩ v
  have hP : |orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z k| ≤
      (K/2)*‖v‖^2*(chainEnergy ls)^2+(S/2)*‖v‖^4 := by
    have H := abs_halved_difference_le hEn hsi
    convert H using 1
    · congr 1
      dsimp only [orderedPathEnergyRemainder,jj,windowEntryIndex]
      ring
    · ring
  have hmain := energy_step_size_le hK hD hh hh1 hn (sq_nonneg ‖v‖)
    (chainEnergy_nonneg ls) hdir henergy
  have hsmall : (S/2)*‖v‖^4≤(eps/2)/(N:ℝ) := by
    have H := quartic_step_size_le hS hD hh.le hn (sq_nonneg ‖v‖) hdir hself
    simpa only [← pow_mul] using H
  have hEnt' := hEnt lam hlam z j k hkE
  rw [massSensitivityRemainder_split]
  exact (abs_add_le _ _).trans ((add_le_add hEnt' (hP.trans (add_le_add hmain hsmall))).trans_eq (by ring))

end SKBarriers2.Corner

namespace SKBarriers2.Corner
local notation "E" => (Fin 3 → ℝ)

theorem massPathRegular_of_indexedEngineInputs
    (l : List (MassPathEntry E)) (f : E → ℝ)
    (hengine : ∀ j : Fin l.length,
      let F := massPathValue (l.drop (j.val+1)) f
      ParamRegular F ∧ ParamRegular (fun z : ℝ × E =>
        ((l.get j).1+z.1*(l.get j).2.1)*F z)) : MassPathRegular l f := by
  induction l with
  | nil => trivial
  | cons q l ih =>
    refine ⟨?_,ih ?_⟩
    · have H := hengine ⟨0,by simp⟩
      simpa only [MovingMassRegular,List.drop_succ_cons,List.drop_zero,List.get_eq_getElem,List.getElem_cons_zero] using H
    · intro j
      have H := hengine ⟨j.val+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using j.isLt⟩
      simpa only [List.drop_succ_cons,List.get_eq_getElem,List.getElem_cons_succ] using H

end SKBarriers2.Corner
