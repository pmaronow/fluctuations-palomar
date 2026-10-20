module

public import SKBarriers2.Analysis.ParamChain
public import SKBarriers2.Corner.MassVariationFinal
public import OAI.Probability.SKBarriers.Calculus.IntervalDifferentiation

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set OAI.SK.Analytic

namespace SKBarriers2.ParamChain

section ParameterMaps

variable {P Q X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
private theorem growth_parameterComp {Y : Type} [Norm Y] {F : P × X → Y}
    (hF : ParamExpGrowth F) (L : Q →L[ℝ] P) :
    ParamExpGrowth (fun z : Q × X => F (L z.1,z.2)) := by
  intro R
  obtain ⟨C,M,hC,hM,hb⟩ := hF (‖L‖*max R 0)
  refine ⟨C,M,hC,hM,?_⟩
  intro p x hp
  exact hb (L p) x ((L.le_opNorm p).trans (mul_le_mul_of_nonneg_left
    (hp.trans (le_max_left _ _)) (norm_nonneg L)))

omit [NormedSpace ℝ X] in
private theorem linear_parameterComp {F : P × X → ℝ}
    (hF : ParamLinearGrowth F) (L : Q →L[ℝ] P) :
    ParamLinearGrowth (fun z : Q × X => F (L z.1,z.2)) := by
  intro R
  obtain ⟨C,hC,hb⟩ := hF (‖L‖*max R 0)
  refine ⟨C,hC,?_⟩
  intro p x hp
  exact hb (L p) x ((L.le_opNorm p).trans (mul_le_mul_of_nonneg_left
    (hp.trans (le_max_left _ _)) (norm_nonneg L)))

theorem regular_parameterComp {F : P × X → ℝ} (hF : ParamRegular F) (L : Q →L[ℝ] P) :
    ParamRegular (fun z : Q × X => F (L z.1,z.2)) := by
  let A : Q × X →L[ℝ] P × X := L.prodMap (ContinuousLinearMap.id ℝ X)
  exact ⟨hF.1.comp A.contDiff,linear_parameterComp hF.2.1 L,
    param_fderiv_compCLM_growth F A id (hF.1.differentiable (by norm_num))
      (growth_parameterComp hF.2.2.1 L),
    param_second_compCLM_growth F A id hF.1 (growth_parameterComp hF.2.2.2 L)⟩

private theorem regular_linearParameter (M : P →L[ℝ] ℝ) :
    ParamRegular (fun z : P × X => M z.1) := by
  let K : P × X →L[ℝ] ℝ := M.comp (ContinuousLinearMap.fst ℝ P X)
  have hd : fderiv ℝ (fun z : P × X => M z.1) = fun _ => K :=
    funext (fun _ => K.fderiv)
  refine ⟨K.contDiff,?_,?_,?_⟩
  · intro R
    refine ⟨‖M‖*max R 0,by positivity,?_⟩
    intro p x hp
    exact ((M.le_opNorm p).trans (mul_le_mul_of_nonneg_left
      (hp.trans (le_max_left _ _)) (norm_nonneg M))).trans
      (le_mul_of_one_le_right (by positivity) (by linarith [norm_nonneg x]))
  · rw [hd]
    exact ParamExpGrowth.of_bounded (norm_nonneg K) (fun _ => le_rfl)
  · rw [hd]
    have hzero : fderiv ℝ (fun _ : P × X => K) =
        fun _ => (0 : P × X →L[ℝ] P × X →L[ℝ] ℝ) :=
      funext (fun _ => fderiv_const_apply K)
    rw [hzero]
    exact ParamExpGrowth.of_bounded
      (f := fun _ : P × X => (0 : P × X →L[ℝ] P × X →L[ℝ] ℝ))
      (C := 0) le_rfl (fun _ => le_of_eq ContinuousLinearMap.opNorm_zero)

theorem regular_mul_linearParameter {F : P × X → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) : ParamRegular (fun z => M z.1*F z) := by
  have H := (regular_linearParameter (X := X) M).toSmooth.mul hF.toSmooth
  refine ⟨H.1,?_,H.2.2⟩
  intro R
  obtain ⟨C,hC,hb⟩ := hF.2.1 R
  refine ⟨(‖M‖*max R 0)*C,by positivity,?_⟩
  intro p x hp
  rw [abs_mul]
  have hm : |M p|≤‖M‖*max R 0 :=
    (M.le_opNorm p).trans (mul_le_mul_of_nonneg_left
      (hp.trans (le_max_left _ _)) (norm_nonneg M))
  exact (mul_le_mul hm (hb p x hp) (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem regular_mul_affineMass {F : ℝ × X → ℝ} (hF : ParamRegular F) (a d : ℝ) :
    ParamRegular (fun z => (a+z.1*d)*F z) := by
  have H := (hF.const_mul a).add
    ((regular_mul_linearParameter hF (ContinuousLinearMap.id ℝ ℝ)).const_mul d)
  convert H using 1
  funext z
  simp only [ContinuousLinearMap.id_apply]
  ring

end ParameterMaps

section CompactAverage

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
private theorem growth_compactAverage {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : (P × ℝ) × X → Y} (hF : ParamExpGrowth F) :
    ParamExpGrowth (fun z : P × X => ∫ t in (0:ℝ)..1, F ((z.1,t),z.2)) := by
  intro R
  obtain ⟨C,M,hC,hM,hb⟩ := hF (max R 1)
  refine ⟨C,M,hC,hM,?_⟩
  intro p x hp
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := C*Real.exp (M*‖x‖))
    (f := fun t => F ((p,t),x)) (fun t ht => by
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at ht
      apply hb (p,t) x
      rw [Prod.norm_def,Real.norm_eq_abs]
      exact max_le (hp.trans (le_max_left _ _))
        ((abs_le.mpr ⟨by linarith [ht.1],ht.2⟩).trans (le_max_right _ _)))
  simpa only [sub_zero,abs_one,mul_one] using H

theorem smooth_compactAverage {F : (P × ℝ) × X → ℝ} (hF : ParamSmooth F) :
    ParamSmooth (fun z : P × X => ∫ t in (0:ℝ)..1, F ((z.1,t),z.2)) := by
  let A : (P × X) × ℝ →L[ℝ] (P × ℝ) × X :=
    ((ContinuousLinearMap.fst ℝ P X).comp (ContinuousLinearMap.fst ℝ (P × X) ℝ) |>.prod
      (ContinuousLinearMap.snd ℝ (P × X) ℝ)).prod
      ((ContinuousLinearMap.snd ℝ P X).comp (ContinuousLinearMap.fst ℝ (P × X) ℝ))
  let J : P × X →L[ℝ] (P × ℝ) × X := A.comp (ContinuousLinearMap.inl ℝ (P × X) ℝ)
  let D : (P × ℝ) × X → (P × X →L[ℝ] ℝ) := fun z => (fderiv ℝ F z).comp J
  let DD : (P × ℝ) × X → (P × X →L[ℝ] P × X →L[ℝ] ℝ) := fun z =>
    ((ContinuousLinearMap.compL ℝ (P × X) ((P × ℝ) × X) ℝ).flip J).comp
      ((fderiv ℝ (fderiv ℝ F) z).comp J)
  have hD : ContDiff ℝ 1 D := (hF.1.fderiv_right (by norm_num)).clm_comp contDiff_const
  have hDD : Continuous DD := by
    exact Continuous.clm_comp continuous_const
      (((hF.1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
        (by norm_num)).clm_comp continuous_const)
  have hR (z : P × X) (t : ℝ) :
      HasFDerivAt (fun w : P × X => ((w.1,t),w.2)) J z := by
    exact ((ContinuousLinearMap.fst ℝ P X).hasFDerivAt.prodMk
      (hasFDerivAt_const t z)).prodMk (ContinuousLinearMap.snd ℝ P X).hasFDerivAt
  have hd (z : P × X) (t : ℝ) : HasFDerivAt (fun w : P × X => F ((w.1,t),w.2))
      (D ((z.1,t),z.2)) z := by
    exact (hF.1.differentiable (by norm_num) _).hasFDerivAt.comp z (hR z t)
  have hdd (z : P × X) (t : ℝ) : HasFDerivAt
      (fun w : P × X => D ((w.1,t),w.2)) (DD ((z.1,t),z.2)) z := by
    let C := (ContinuousLinearMap.compL ℝ (P × X) ((P × ℝ) × X) ℝ).flip J
    have H := C.hasFDerivAt.comp ((z.1,t),z.2)
      ((hF.1.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) ((z.1,t),z.2)).hasFDerivAt
    exact H.comp z (hR z t)
  have hI (z : P × X) : HasFDerivAt
      (fun w : P × X => ∫ t in (0:ℝ)..1, F ((w.1,t),w.2))
      (∫ t in (0:ℝ)..1, D ((z.1,t),z.2)) z :=
    hasFDerivAt_intervalIntegral (fun z t => F ((z.1,t),z.2))
      (fun z t => D ((z.1,t),z.2)) (hF.1.continuous.comp A.continuous)
      (hD.continuous.comp A.continuous) hd 0 1 z
  have hII (z : P × X) : HasFDerivAt
      (fun w : P × X => ∫ t in (0:ℝ)..1, D ((w.1,t),w.2))
      (∫ t in (0:ℝ)..1, DD ((z.1,t),z.2)) z :=
    hasFDerivAt_intervalIntegral (fun z t => D ((z.1,t),z.2))
      (fun z t => DD ((z.1,t),z.2)) (hD.continuous.comp A.continuous)
      (hDD.comp A.continuous) hdd 0 1 z
  have he : fderiv ℝ (fun w : P × X => ∫ t in (0:ℝ)..1, F ((w.1,t),w.2)) =
      fun z => ∫ t in (0:ℝ)..1, D ((z.1,t),z.2) := funext (fun z => (hI z).fderiv)
  have hee : fderiv ℝ (fderiv ℝ (fun w : P × X => ∫ t in (0:ℝ)..1, F ((w.1,t),w.2))) =
      fun z => ∫ t in (0:ℝ)..1, DD ((z.1,t),z.2) := by
    rw [he]
    exact funext (fun z => (hII z).fderiv)
  refine ⟨contDiff_intervalIntegral 2 (fun z => F (A z)) (hF.1.comp A.contDiff) 0 1,
    growth_compactAverage hF.2.1,?_,?_⟩
  · rw [he]
    exact growth_compactAverage (hF.2.2.1.of_norm_le (norm_nonneg J)
      (fun z => (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)))
  · rw [hee]
    apply growth_compactAverage
    apply hF.2.2.2.of_norm_le (K := ‖J‖*‖J‖) (by positivity)
    intro z
    let C := (ContinuousLinearMap.compL ℝ (P × X) ((P × ℝ) × X) ℝ).flip J
    have hC : ‖C‖≤‖J‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg J)
      intro T
      exact (ContinuousLinearMap.opNorm_comp_le T J).trans_eq (mul_comm _ _)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hC (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _) (norm_nonneg J)).trans_eq (by ring))

end CompactAverage

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

section SignedMasses

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem step_eq_compactTiltedMean {f : X → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v x : X) :
    vectorStep m v f x = ∫ t in (0:ℝ)..1, vectorStepAverage (t*m) v f f x := by
  let hb := hf.compCLM (vectorTranslation v)
  let c : ℝ → ℝ := cgf (fun y : ℝ => f (x+y • v)) (gaussianReal 0 1)
  have hmean (a : ℝ) : HasDerivAt c (vectorStepAverage a v f f x) a := by
    have H := (analyticAt_cgf (hb.mem_interior_integrableExpSet_section x a)).differentiableAt.hasDerivAt
    rw [← integral_tilted_mul_self (hb.mem_interior_integrableExpSet_section x a)] at H
    exact H
  have hc : Continuous (fun a => vectorStepAverage a v f f x) := by
    have he : (fun a => vectorStepAverage a v f f x) = deriv c :=
      funext (fun a => (hmean a).deriv.symm)
    rw [he]
    exact continuous_iff_continuousAt.mpr (fun a =>
      (analyticAt_cgf (hb.mem_interior_integrableExpSet_section x a)).deriv.continuousAt)
  by_cases hm : m=0
  · subst m
    simp only [mul_zero, vectorStepAverage, OAI.SK.Analytic.gaussianAverage, gaussianStepLaw_zero,
      vectorStep, gaussianStep, ite_true, intervalIntegral.integral_const, sub_zero, one_smul]
  · have hd (t : ℝ) : HasDerivAt (fun t => c (t*m))
        (m*vectorStepAverage (t*m) v f f x) t := by
      convert! (hmean (t*m)).comp t ((hasDerivAt_id t).mul_const m) using 1
      ring
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((continuous_const.mul (hc.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_const_mul] at H
    have he : c m = m*vectorStep m v f x := by
      simp only [c,vectorStep,gaussianStep,hm,ite_false,positiveGaussianLogStep,cgf,mgf]
      field_simp
    simp only [one_mul,zero_mul,cgf_zero,c,sub_zero] at H
    change m*(∫ t in (0:ℝ)..1, vectorStepAverage (t*m) v f f x) = c m at H
    rw [he] at H
    exact (mul_left_cancel₀ hm H).symm

theorem monotone_massStep {f : X → ℝ} (hf : BoundedDerivs f) (v x : X) :
    Monotone (fun m : ℝ => vectorStep m v f x) := by
  let hb := hf.compCLM (vectorTranslation v)
  let c := cgf (fun y : ℝ => f (x+y • v)) (gaussianReal 0 1)
  have hcv : ConvexOn ℝ univ c := by
    apply convexOn_log_integral_exp (gaussianReal 0 1) (fun m y => m*f (x+y • v))
    · intro m
      exact hb.exp_integrable m x
    · intro y
      refine ⟨convex_univ,?_⟩
      intro a _ b _ u w _ _ _
      simp only [smul_eq_mul]
      exact le_of_eq (by ring)
  have hd : DifferentiableAt ℝ c 0 :=
    (analyticAt_cgf (hb.mem_interior_integrableExpSet_section x 0)).differentiableAt
  change Monotone (fun m => gaussianStep m (fun z => f ((vectorTranslation v) z)) x)
  rw [gaussianStep_mass_eq_dslope hb x]
  change Monotone (dslope c 0)
  intro a b hab
  by_cases ha : a=0
  · subst a
    by_cases hb : b=0
    · subst b
      exact le_rfl
    · rw [dslope_same,dslope_of_ne _ hb]
      exact hcv.deriv_le_slope (mem_univ _) (mem_univ _) (lt_of_le_of_ne hab (Ne.symm hb)) hd
  · by_cases hb : b=0
    · subst b
      rw [dslope_of_ne _ ha,dslope_same,slope_comm]
      exact hcv.slope_le_deriv (mem_univ _) (mem_univ _) (lt_of_le_of_ne hab ha) hd
    · rw [dslope_of_ne _ ha,dslope_of_ne _ hb]
      exact hcv.slope_mono (mem_univ _) ⟨mem_univ _,ha⟩ ⟨mem_univ _,hb⟩ hab

theorem linear_affineMassStep {F : ℝ × X → ℝ} (hF : ParamRegular F)
    (hsection : ∀ p : ℝ, BoundedDerivs (fun y => F (p,y))) (a d : ℝ) (v : X) :
    ParamLinearGrowth (fun z : ℝ × X => vectorStep (a+z.1*d) v (fun y => F (z.1,y)) z.2) := by
  intro R
  let M := |a|+max R 0*|d|+1
  have hT := hF.fieldComp (vectorTranslation v)
  obtain ⟨C,hC,hplus⟩ := (hT.gaussianStep M).2.1 R
  obtain ⟨D,hD,hminus⟩ := (hT.gaussianStep (-M)).2.1 R
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro p x hp
  have hpabs : |p| ≤ max R 0 := by
    simpa only [Real.norm_eq_abs] using hp.trans (le_max_left R 0)
  have hmp : |a+p*d|≤M := by
    calc
      _ ≤ |a|+|p*d| := abs_add_le _ _
      _ = |a|+|p| *|d| := by rw [abs_mul]
      _ ≤ |a|+max R 0*|d| := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hpabs (abs_nonneg d))
      _ ≤ M := by dsimp only [M]; linarith
  have hlo := monotone_massStep (hsection p) v x (abs_le.mp hmp).1
  have hhi := monotone_massStep (hsection p) v x (abs_le.mp hmp).2
  have hp' := hplus p x hp
  have hm' := hminus p x hp
  change |vectorStep M v (fun y => F (p,y)) x|≤C*(1+‖x‖) at hp'
  change |vectorStep (-M) v (fun y => F (p,y)) x|≤D*(1+‖x‖) at hm'
  exact abs_le.mpr ⟨by nlinarith [(abs_le.mp hm').1,mul_nonneg hC (by positivity : 0≤1+‖x‖)],
    by nlinarith [(abs_le.mp hp').2,mul_nonneg hD (by positivity : 0≤1+‖x‖)]⟩

end SignedMasses

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

section AffineSteps

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem regular_affineMassStep {F : ℝ × X → ℝ} (hF : ParamRegular F)
    (hsection : ∀ p : ℝ, BoundedDerivs (fun y => F (p,y))) (a d : ℝ) (v : X) :
    ParamRegular (fun z : ℝ × X => vectorStep (a+z.1*d) v (fun y => F (z.1,y)) z.2) := by
  let F2 : (ℝ × ℝ) × X → ℝ := fun z => F (z.1.1,z.2)
  let M : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let T : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hF2 : ParamRegular F2 := regular_parameterComp hF M
  let W : (ℝ × ℝ) × X → ℝ := fun z => (a+z.1.1*d)*F2 z
  have hW : ParamRegular W := by
    have H := (hF2.const_mul a).add ((regular_mul_linearParameter hF2 M).const_mul d)
    convert H using 1
    funext z
    dsimp only [W,F2,M]
    simp only [ContinuousLinearMap.coe_fst']
    ring
  let H : (ℝ × ℝ) × X → ℝ := fun z => z.1.2*W z
  have hH : ParamRegular H := regular_mul_linearParameter hW T
  have hA : ParamSmooth (fun z : (ℝ × ℝ) × X =>
      vectorStepAverage (z.1.2*(a+z.1.1*d)) v (fun y => F (z.1.1,y))
        (fun y => F (z.1.1,y)) z.2) := by
    have K := ParamSmooth.gaussianAverage (hH.fieldComp (vectorTranslation v))
      (hF2.fieldComp (vectorTranslation v)).toSmooth 1
    convert K using 1
    funext z
    simp only [vectorStepAverage,OAI.SK.Analytic.gaussianAverage,gaussianStepLaw,H,W,F2,
      vectorTranslation,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      add_apply,ContinuousLinearMap.smulRight_apply,one_mul,mul_assoc]
  have hI := smooth_compactAverage hA
  have he : (fun z : ℝ × X => ∫ t in (0:ℝ)..1,
      vectorStepAverage (t*(a+z.1*d)) v (fun y => F (z.1,y)) (fun y => F (z.1,y)) z.2) =
      fun z => vectorStep (a+z.1*d) v (fun y => F (z.1,y)) z.2 := by
    funext z
    exact (step_eq_compactTiltedMean (hsection z.1) _ v z.2).symm
  rw [he] at hI
  exact ⟨hI.1,linear_affineMassStep hF hsection a d v,hI.2.2⟩

omit [FiniteDimensional ℝ X] in
theorem affineMass_hasDerivAt_zero {f : X → ℝ} (hf : BoundedDerivs f)
    {a d p : ℝ} (hzero : a+p*d=0) (v x : X) :
    HasDerivAt (fun t => vectorStep (a+t*d) v f x)
      (d*variance (fun y : ℝ => f (x+y • v)) (gaussianReal 0 1)/2) p := by
  have hmass : HasDerivAt (fun t : ℝ => a+t*d) d p := by
    convert! (((hasDerivAt_id p).mul_const d).const_add a) using 1
    ring
  have hz : HasDerivAt (fun m : ℝ => vectorStep m v f x)
      (variance (fun y : ℝ => f (x+y • v)) (gaussianReal 0 1)/2) (a+p*d) := by
    rw [hzero]
    exact gaussianStep_hasDerivAt_mass_zero (hf.compCLM (vectorTranslation v)) x
  convert! hz.comp p hmass using 1
  ring

end AffineSteps

end SKBarriers2.ParamChain

namespace SKBarriers2.Corner

local notation "E" => (Fin 3 → ℝ)

theorem regular_massPathValue {B : ℝ} {f : E → ℝ} (hf : QPotential 2 B f)
    (l : List (MassPathEntry E)) : ParamRegular (massPathValue l f) := by
  induction l with
  | nil => exact ParamChain.regular_fixedTerminal hf le_rfl ℝ
  | cons p l ih =>
    have hsection (t : ℝ) : BoundedDerivs (fun y => massPathValue l f (t,y)) :=
      vectorIncrementChain_regular (massPath l t) (hf.boundedDerivs le_rfl)
    exact ParamChain.regular_affineMassStep ih hsection p.1 p.2.1 p.2.2

theorem massPathRegular_of_qPotential {B : ℝ} {f : E → ℝ} (hf : QPotential 2 B f)
    (l : List (MassPathEntry E)) : MassPathRegular l f := by
  induction l with
  | nil => trivial
  | cons p l ih =>
    have hF := regular_massPathValue hf l
    exact ⟨⟨hF,ParamChain.regular_mul_affineMass hF p.1 p.2.1⟩,ih⟩

theorem scalarData_uniformMassPathRegularity {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    UniformMassPathRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  have hu1 : u < 1 := hu.trans D.q_mem.2
  refine ⟨(1-u)/3,1/2,by positivity,by norm_num,?_⟩
  intro r hr h hh hh0 N _ k _
  have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
    constructor <;> linarith [hr.1,hr.2]
  exact massPathRegular_of_qPotential (scalarData_massVariationTerminal_qPotential D 2 ht) _

theorem massVariationBound_of_scalarData_C2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hC2 : MassSensitivityC2 β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact massVariationBound_of_scalarData_C2_and_path D hl hu hC2
    (scalarData_uniformMassPathRegularity D hl hu)

end SKBarriers2.Corner
