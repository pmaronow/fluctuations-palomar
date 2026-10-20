module
public import SKConstants.ParisiFiniteTanhTail

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic
set_option maxHeartbeats 1000000

lemma scalarDefect_boundedSmooth : BoundedSmooth scalarDefect := by
  have H := (regularDatum_softAbs (by norm_num : (1:ℝ)≠0)).deriv_bounded.deriv
  convert H using 1
  funext x
  rw [show deriv (softAbs 1)=Real.tanh from by
    funext y
    simpa using (hasDerivAt_softAbs (by norm_num : (1:ℝ)≠0) y).deriv]
  exact (hasDerivAt_tanh_scalar x).deriv.symm

lemma varianceLogHeat_one_softAbs {t : ℝ} (ht : 0 ≤ t) :
    varianceLogHeat 1 t (softAbs 1) = fun x => softAbs 1 x+t/2 := by
  funext x
  rw [varianceLogHeat_eq_logSemigroup_toNNReal
    (regularDatum_softAbs (by norm_num : (1:ℝ)≠0)).smooth.continuous.measurable]
  have H := congrFun (logSemigroup_one_softAbs_add (Real.toNNReal t) 0) x
  simpa only [add_zero,Real.coe_toNNReal _ ht] using H

lemma deriv_varianceLogHeat_one_softAbs {t : ℝ} (ht : 0 ≤ t) :
    deriv (varianceLogHeat 1 t (softAbs 1))=Real.tanh := by
  rw [varianceLogHeat_one_softAbs ht]
  funext x
  simpa using ((hasDerivAt_softAbs (by norm_num : (1:ℝ)≠0) x).add_const (t/2)).deriv

theorem shapedTanhDensity_postKernel_moment_ge {L : ℝ → ℝ} (hL : RegularDatum L)
    {K : ℝ≥0} (hLip : LipschitzWith K L) (hshape : ForwardDatumShape L)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (3/4:ℝ)*(∫ x, Real.exp (softAbs 1 x-x^2/(2*a)+L x)*
      varianceTilted 1 t (softAbs 1) (fun y => (scalarDefect y)^2) x) ≤
      ∫ x, Real.exp (softAbs 1 x-x^2/(2*a)+L x)*
        varianceTilted 1 t (softAbs 1) (fun y => (scalarDefect y)^3) x := by
  let L' := forwardCorrection a L t
  have hL' := forwardCorrection_regular ha hL hLip t
  have hshape' := forwardCorrection_shape ha hL hLip hshape ht.le
  let w := gaussianLogDensity (1/(2*(a+t))) L'
  have hd : 0 < 1/(2*(a+t)) := by positivity
  have hwc : Continuous w := gaussianLogDensity_continuous hL'.smooth.continuous _
  have hwm : AntitoneOn w (Ici (0:ℝ)) :=
    gaussianLogDensity_antitoneOn_of_even_concave hL' hshape'.even hshape'.second hd.le
  have H := scalarEvenDecreasingWeight_sech_fifth_ge_three_quarters_third
    w hwc.measurable (fun x => (gaussianLogDensity_pos _ _ x).le)
      (gaussianLogDensity_even hshape'.even _) hwm
  have heq (k : ℕ) :
      (∫ x, Real.exp (softAbs 1 x-x^2/(2*a)+L x)*
        varianceTilted 1 t (softAbs 1) (fun y => (scalarDefect y)^(k+1)) x) =
        (2*Real.exp (-t/2))*(∫ y, w y*(scalarSech y)^(2*k+1)) := by
    have hg := scalarDefect_boundedSmooth.pow (k+1)
    have HF := density_tilted_pairing hLip
      (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) hg ha ht (by norm_num : (1:ℝ)≠0)
    simp only [one_mul,varianceLogHeat_one_softAbs ht.le] at HF
    have hn (x : ℝ) : Real.exp (softAbs 1 x-x^2/(2*a)+L x) =
        Real.exp (-t/2)*Real.exp (softAbs 1 x+t/2-x^2/(2*a)+L x) := by
      rw [←Real.exp_add]
      congr 1
      ring
    simp_rw [hn,mul_assoc]
    rw [integral_const_mul,HF]
    rw [show 2*(Real.exp (-t/2)*(∫ y,w y*(scalarSech y)^(2*k+1))) =
      Real.exp (-t/2)*(2*(∫ y,w y*(scalarSech y)^(2*k+1))) by ring]
    congr 1
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    have hex : Real.exp (softAbs 1 y-y^2/(2*(a+t))+L' y) =
        2*Real.cosh y*w y := by
      dsimp [w,gaussianLogDensity]
      have E : softAbs 1 y-y^2/(2*(a+t))+L' y=
          softAbs 1 y+(-(1/(2*(a+t)))*y^2+L' y) := by ring
      rw [E,Real.exp_add]
      simp only [softAbs,one_mul,div_one]
      rw [Real.exp_log (mul_pos (by norm_num) (Real.cosh_pos y))]
    change Real.exp (softAbs 1 y-y^2/(2*(a+t))+L' y)*(scalarDefect y)^(k+1) = _
    rw [hex]
    calc
      _ = 2*w y*(Real.cosh y*(scalarDefect y)^(k+1)) := by ring
      _ = _ := by rw [cosh_mul_scalarDefect_pow]; ring
  have he2 := heq 1
  have he3 := heq 2
  norm_num only at he2 he3
  rw [he2,he3]
  have HH := mul_le_mul_of_nonneg_left H (show 0 ≤ 2*Real.exp (-t/2) by positivity)
  nlinarith [HH]

theorem finiteFeedback_postKernel_moment_ge {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hcap : ∀ i, (c i:ℝ) ≤ 1)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) (hi : 0 < i) (hiN : i ≤ N)
    (hci : c i=1) (htail : ∀ j, i ≤ j → j < N → c j=1)
    {t : ℝ} (ht : 0 < t) :
    (3/4:ℝ)*(∫ w, varianceTilted 1 t (softAbs 1) (fun y => (scalarDefect y)^2)
      ((finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
        (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) c h N 0).solution
          W.driver ((i:ℝ≥0)*h) w) ∂W.law) ≤
      ∫ w, varianceTilted 1 t (softAbs 1) (fun y => (scalarDefect y)^3)
        ((finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
          (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) c h N 0).solution
            W.driver ((i:ℝ≥0)*h) w) ∂W.law := by
  have hf := regularDatum_softAbs (by norm_num : (1:ℝ)≠0)
  have hLip := softAbs_lipschitz (by norm_num : (1:ℝ)≠0)
  have hg2 := (varianceTilted_family hf hLip (scalarDefect_boundedSmooth.pow 2)
    (by norm_num : (0:ℝ)≤1)).regular t
  have hg3 := (varianceTilted_family hf hLip (scalarDefect_boundedSmooth.pow 3)
    (by norm_num : (0:ℝ)≤1)).regular t
  rw [finite_density_identity W hf hLip hg2 c hc hh hi hiN,
    finite_density_identity W hf hLip hg3 c hc hh hi hiN]
  let L := forwardBoundary c h (softAbs 1) N i
  have hL := forwardBoundary_regular hf hLip c hh N i
  obtain ⟨K,hK⟩ := hL.exists_lipschitz
  have H := shapedTanhDensity_postKernel_moment_ge hL hK
    (forwardBoundary_shape c hc hmono hcap hh N i)
    (mul_pos (Nat.cast_pos.mpr hi) hh) ht
  have heq (g : ℝ → ℝ) :
      (∫ x, finiteDensity c h (softAbs 1) N i x*g x) =
        Real.exp ((N-i:ℕ)*(h:ℝ)/2)*(∫ x, Real.exp (softAbs 1 x-
          x^2/(2*((i:ℝ)*(h:ℝ)))+L x)*g x) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    unfold finiteDensity
    rw [hci,NNReal.coe_one,one_mul,backwardBoundary_softAbs_one_tail c h N i hiN htail]
    conv_rhs => rw [←mul_assoc,←Real.exp_add]
    congr 2
    dsimp only [L]
    ring
  rw [heq,heq]
  change (3/4:ℝ)*(Real.exp ((N-i:ℕ)*(h:ℝ)/2)*_) ≤ Real.exp ((N-i:ℕ)*(h:ℝ)/2)*_
  have HH := mul_le_mul_of_nonneg_left H (Real.exp_pos ((N-i:ℕ)*(h:ℝ)/2)).le
  dsimp only [L] at *
  nlinarith [HH]

end SKConstants.ParisiFullSupport
