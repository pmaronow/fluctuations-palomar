module
public import SKConstants.ParisiFiniteCDFBridge
public import SKConstants.ParisiFiniteDualWeight
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.ScalarMassOne
public import SKConstants.ScalarSechMomentRatio

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic
set_option maxHeartbeats 1000000

lemma softAbs_one_eq_spinTerminal : softAbs 1 = scalarSpinTerminal := by
  funext x
  simp [softAbs,scalarSpinTerminal]

lemma logSemigroup_one_softAbs_add (h : ℝ≥0) (a : ℝ) :
    logSemigroup 1 h (fun x => softAbs 1 x+a) =
      fun x => softAbs 1 x+a+(h:ℝ)/2 := by
  have hf : BoundedDerivs scalarSpinTerminal := scalarHierarchy_spin_regular 0 Fin.elim0 Fin.elim0
  have he : Real.toNNReal ((Real.sqrt (h:ℝ))^2) = h := by
    rw [Real.sq_sqrt h.coe_nonneg,Real.toNNReal_coe]
  rw [softAbs_one_eq_spinTerminal]
  have HH := scalarStep_eq_logSemigroup (f := fun x => scalarSpinTerminal x+a)
    (hf.1.continuous.measurable.add measurable_const) 1 (Real.sqrt (h:ℝ))
  rw [he] at HH
  rw [←HH]
  rw [scalarStep_add_const hf,scalarStep_one_spin]
  funext x
  rw [Real.sq_sqrt h.coe_nonneg]
  ring

lemma cascade_softAbs_one_tail (c : ℕ → ℝ≥0) (h : ℝ≥0) (n k : ℕ)
    (hc : ∀ j, k ≤ j → j < k+n → c j=1) :
    cascade c h (softAbs 1) n k = fun x => softAbs 1 x+(n:ℝ)*(h:ℝ)/2 := by
  induction n generalizing k with
  | zero => simp [cascade]
  | succ n ih =>
    have hk := hc k le_rfl (by omega)
    have hn : ∀ j, k+1 ≤ j → j < k+1+n → c j=1 := by
      intro j hj hjn
      exact hc j (by omega) (by omega)
    change logSemigroup (c k) h (cascade c h (softAbs 1) n (k+1)) = _
    rw [hk,NNReal.coe_one,ih (k+1) hn,logSemigroup_one_softAbs_add]
    funext x
    push_cast
    ring

lemma backwardBoundary_softAbs_one_tail (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    (hiN : i ≤ N) (hc : ∀ j, i ≤ j → j < N → c j=1) :
    backwardBoundary c h (softAbs 1) N i =
      fun x => softAbs 1 x+(N-i:ℕ)*(h:ℝ)/2 := by
  exact cascade_softAbs_one_tail c h (N-i) i (by
    intro j hj hjN
    exact hc j hj (by omega))

lemma finiteDensity_tanh_tail (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ)
    (hiN : i ≤ N) (hi : c i=1) (hc : ∀ j, i ≤ j → j < N → c j=1) (x : ℝ) :
    finiteDensity c h (softAbs 1) N i x =
      (2*Real.exp ((N-i:ℕ)*(h:ℝ)/2))*finiteTanhDualWeight c h N i x*Real.cosh x := by
  rw [finiteDensity,hi,NNReal.coe_one,one_mul,
    backwardBoundary_softAbs_one_tail c h N i hiN hc]
  unfold finiteTanhDualWeight gaussianLogDensity
  simp only [softAbs,one_mul,div_one]
  have H : Real.log (2*Real.cosh x)+(N-i:ℕ)*(h:ℝ)/2-x^2/(2*((i:ℝ)*(h:ℝ)))+
      forwardBoundary c h (softAbs 1) N i x =
      Real.log (2*Real.cosh x)+(N-i:ℕ)*(h:ℝ)/2+
        (-(1/(2*(i:ℝ)*(h:ℝ)))*x^2+forwardBoundary c h (softAbs 1) N i x) := by
    ring
  rw [H,Real.exp_add,Real.exp_add,
    Real.exp_log (mul_pos (by norm_num) (Real.cosh_pos x))]
  ring

lemma cosh_mul_scalarDefect_pow (x : ℝ) (k : ℕ) :
    Real.cosh x*(scalarDefect x)^(k+1) = (scalarSech x)^(2*k+1) := by
  rw [scalarDefect_eq_scalarSech_sq]
  have hc := (Real.cosh_pos x).ne'
  have H : Real.cosh x*(scalarSech x)^2 = scalarSech x := by
    unfold scalarSech
    field_simp
  calc
    _ = (Real.cosh x*(scalarSech x)^2)*((scalarSech x)^2)^k := by
      rw [pow_succ]; ring
    _ = scalarSech x*((scalarSech x)^2)^k := by rw [H]
    _ = _ := by rw [←pow_mul,pow_succ]; ring

theorem finiteFeedback_tanh_third_moment_ge {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hcap : ∀ i, (c i:ℝ) ≤ 1)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) (hi : 0 < i) (hiN : i ≤ N)
    (hci : c i=1) (htail : ∀ j, i ≤ j → j < N → c j=1) :
    (3/4:ℝ)*(∫ w, (scalarDefect ((finiteFeedback
      (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
      (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) c h N 0).solution
        W.driver ((i:ℝ≥0)*h) w))^2 ∂W.law) ≤
      ∫ w, (scalarDefect ((finiteFeedback
      (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
      (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) c h N 0).solution
        W.driver ((i:ℝ≥0)*h) w))^3 ∂W.law := by
  have hg : BoundedSmooth scalarDefect := by
    have H := (regularDatum_softAbs (by norm_num : (1:ℝ)≠0)).deriv_bounded.deriv
    convert H using 1
    funext x
    rw [show deriv (softAbs 1)=Real.tanh from by
      funext y
      simpa using (hasDerivAt_softAbs (by norm_num : (1:ℝ)≠0) y).deriv]
    exact (hasDerivAt_tanh_scalar x).deriv.symm
  rw [finite_density_identity W (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
      (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) (hg.pow 2) c hc hh hi hiN,
    finite_density_identity W (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
      (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) (hg.pow 3) c hc hh hi hiN]
  obtain ⟨hp,he,hcont,hint,hm⟩ := finiteTanhDualWeight_shape c hc hmono hcap hh N i hi
  have H := scalarEvenDecreasingWeight_sech_fifth_ge_three_quarters_third
    (finiteTanhDualWeight c h N i) hcont.measurable (fun x => (hp x).le) he hm
  have heq (k : ℕ) :
      (∫ x, finiteDensity c h (softAbs 1) N i x*(scalarDefect x)^(k+1)) =
        (2*Real.exp ((N-i:ℕ)*(h:ℝ)/2))*(∫ x, finiteTanhDualWeight c h N i x*(scalarSech x)^(2*k+1)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [finiteDensity_tanh_tail c h N i hiN hci htail x]
    calc
      _ = (2*Real.exp ((N-i:ℕ)*(h:ℝ)/2))*finiteTanhDualWeight c h N i x*
          (Real.cosh x*(scalarDefect x)^(k+1)) := by ring
      _ = _ := by rw [cosh_mul_scalarDefect_pow]; ring
  have he2 := heq 1
  have he3 := heq 2
  norm_num only at he2 he3
  rw [he2,he3]
  nlinarith [mul_nonneg (show 0 ≤ 2*Real.exp ((N-i:ℕ)*(h:ℝ)/2) by positivity)
    (show 0 ≤ (∫ x, finiteTanhDualWeight c h N i x*(scalarSech x)^5)-
      (3/4:ℝ)*(∫ x, finiteTanhDualWeight c h N i x*(scalarSech x)^3) by linarith [H])]

end SKConstants.ParisiFullSupport
