module

public import SKConstants.Completion.N9Z2.Node
public import SKConstants.Completion.N9Q2.Node
public import SKConstants.Completion.N19.Stability
public import SKConstants.ScalarWeightedPathStability
public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-! Driver stability for the actual fresh-endpoint experiment. The integral
Gronwall argument is adapted from `FourPapersCommon/IntegralGronwall.lean` and
`FourPapersCommon/IntegralPicardTwoDriverGronwall.lean` in the all-lean donor.
Only the additive drivers are perturbed; the drift is the actual Picard drift. -/

/-
MIT License
Copyright (c) 2026 P. M. Aronow

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.L1
open SKConstantsOAI.ZeroTemperatureSK M1 LFine N9Z2 N9Q2

/-- Integral Gronwall only differentiates the continuous error primitive.
The drift in its applications may be merely measurable in time. -/
theorem le_exp_of_integral_le (F : ℝ → ℝ) (hF : Continuous F) (T E L : ℝ)
    (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hF0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ F t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T, F t ≤ E+L*(∫ s in 0..t, F s)) :
    ∀ t ∈ Icc (0 : ℝ) T, F t ≤ E*Real.exp (L*t) := by
  let U : ℝ → ℝ := fun t => E+L*(∫ s in 0..t, F s)
  have hU0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ U t := by
    intro t ht
    exact add_nonneg hE (mul_nonneg hL (intervalIntegral.integral_nonneg ht.1
      (fun s hs => hF0 s ⟨hs.1,hs.2.trans ht.2⟩)))
  have hder : ∀ t, HasDerivAt U (L*F t) t := by
    intro t
    convert! (hasDerivAt_const t E).add
      ((intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 t)
        hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt).const_mul L)
      using 1 <;> simp only [zero_add]
  have hU : Continuous U := continuous_iff_continuousAt.mpr fun t => (hder t).continuousAt
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := U)
    (f' := fun t => L*F t) (a := (0 : ℝ)) (b := T) hU.continuousOn
    (fun t _ => (hder t).hasDerivWithinAt) (δ := E) (K := L) (ε := 0)
    (by simp [U,Real.norm_of_nonneg hE])
    (by
      intro t ht
      rw [Real.norm_of_nonneg (mul_nonneg hL (hF0 t ⟨ht.1,ht.2.le⟩)),
        Real.norm_of_nonneg (hU0 t ⟨ht.1,ht.2.le⟩),add_zero]
      exact mul_le_mul_of_nonneg_left (hineq t ⟨ht.1,ht.2.le⟩) hL)
  intro t ht
  exact (hineq t ht).trans (by
    simpa only [Real.norm_of_nonneg (hU0 t ht),gronwallBound_ε0,sub_zero] using hg t ht)

/-- The actual convergent Picard callback has the sharp additive-driver
stability factor `exp(lip*t)`, with no extra factor two or inflated rate. -/
theorem scalarForwardPicardPath_driver_bound
    (b : BoundedLipschitzDrift) (T : ℝ≥0) (p q : ℝ × ScalarContinuousPath T)
    (E : ℝ) (hE : 0 ≤ E)
    (hdriver : ∀ t, |(p.1+p.2 t)-(q.1+q.2 t)| ≤ E)
    (t : Icc (0 : ℝ) (T : ℝ)) :
    |scalarForwardPicardPath b T p t-scalarForwardPicardPath b T q t| ≤
      E*Real.exp ((b.lip : ℝ)*t) := by
  let X := IccExtend T.coe_nonneg (scalarForwardPicardPath b T p)
  let Y := IccExtend T.coe_nonneg (scalarForwardPicardPath b T q)
  have hX : Continuous X := (scalarForwardPicardPath b T p).continuous.Icc_extend'
  have hY : Continuous Y := (scalarForwardPicardPath b T q).continuous.Icc_extend'
  have hi (Z : ℝ → ℝ) (hZ : Continuous Z) (u : ℝ) :
      IntervalIntegrable (fun s => b.f s (Z s)) volume 0 u := by
    apply (intervalIntegrable_const (c := (b.bound : ℝ))).mono_fun
    · exact (b.measurable.comp (measurable_id.prodMk hZ.measurable)).aestronglyMeasurable
    · exact ae_of_all _ fun s => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg b.bound.coe_nonneg] using b.bounded s (Z s)
  have hineq : ∀ u ∈ Icc (0 : ℝ) (T : ℝ),
      |X u-Y u| ≤ E+(b.lip : ℝ)*(∫ s in 0..u, |X s-Y s|) := by
    intro u hu
    have hp := scalarForwardPicardPath_integral_equation b T p ⟨u,hu⟩
    have hq := scalarForwardPicardPath_integral_equation b T q ⟨u,hu⟩
    have he : X u-Y u = (p.1+p.2 ⟨u,hu⟩-(q.1+q.2 ⟨u,hu⟩))+
        ∫ s in 0..u, b.f s (X s)-b.f s (Y s) := by
      rw [intervalIntegral.integral_sub (hi X hX u) (hi Y hY u)]
      dsimp only [X,Y,IccExtend,Function.comp_apply]
      rw [projIcc_of_mem _ hu]
      dsimp only [IccExtend,Function.comp_apply] at hp hq
      linarith
    rw [he]
    calc
      _ ≤ |p.1+p.2 ⟨u,hu⟩-(q.1+q.2 ⟨u,hu⟩)|+
          |∫ s in 0..u, b.f s (X s)-b.f s (Y s)| := abs_add_le _ _
      _ ≤ E+∫ s in 0..u, |b.f s (X s)-b.f s (Y s)| := by
        apply add_le_add (hdriver ⟨u,hu⟩)
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm
            (f := fun s => b.f s (X s)-b.f s (Y s)) hu.1
      _ ≤ E+∫ s in 0..u, (b.lip : ℝ)*|X s-Y s| := by
        apply add_le_add le_rfl
        apply intervalIntegral.integral_mono_on hu.1 ((hi X hX u).sub (hi Y hY u)).norm
          (((hX.sub hY).abs.intervalIntegrable 0 u).const_mul (b.lip : ℝ))
        intro s _
        simpa only [Real.dist_eq,Real.norm_eq_abs,Pi.sub_apply] using
          (b.lipschitz s).dist_le_mul (X s) (Y s)
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hg := le_exp_of_integral_le (fun u => |X u-Y u|) (hX.sub hY).abs T E b.lip
    hE b.lip.coe_nonneg (fun _ _ => abs_nonneg _) hineq t t.property
  simpa only [X,Y,IccExtend,Function.comp_apply,projIcc_of_mem _ t.property] using hg

/-- For an increasing nonpositive coefficient, the Stieltjes variation and
terminal absolute value add to the absolute value at the start. -/
theorem weightedPath_nonpos_driver_bound (f : StieltjesFunction ℝ) (hf : Continuous f)
    (hf0 : ∀ t, f t ≤ 0) (T : ℝ≥0) (B C : ScalarContinuousPath T) :
    ‖scalarStieltjesWeightedPath f hf T B-scalarStieltjesWeightedPath f hf T C‖ ≤
      (-f 0)*‖B-C‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (neg_nonneg.mpr (hf0 0))
    (norm_nonneg (B-C)))).mpr
  intro t
  have hh := scalarStieltjesWeightedPath_difference_le f hf T B C t
  rw [abs_of_nonpos (hf0 t)] at hh
  convert hh using 1 <;> ring

/-- Changing the standardized endpoint changes the completed current bridge
by at most `sqrt(h)` times the endpoint displacement, uniformly in time. -/
theorem queryBridge_endpoint_norm_bound (h : ℝ≥0) (hh : 0 < h)
    (c : ScalarContinuousPath h) (x y : ℝ) :
    ‖scalarQueryBridgeComplete h (x,c)-scalarQueryBridgeComplete h (y,c)‖ ≤
      Real.sqrt h*|x-y| := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).mpr
  intro t
  have hhR : 0 < (h : ℝ) := hh
  have hr0 : 0 ≤ (t : ℝ)/(h : ℝ) := div_nonneg t.property.1 h.coe_nonneg
  have hr1 : (t : ℝ)/(h : ℝ) ≤ 1 := (div_le_one hhR).mpr t.property.2
  have he : scalarQueryBridgeComplete h (x,c) t-scalarQueryBridgeComplete h (y,c) t =
      ((t : ℝ)/(h : ℝ))*(Real.sqrt h*(x-y)) := by
    change (scalarPinnedBridge h c t+(t : ℝ)/(h : ℝ)*(Real.sqrt h*x))-
      (scalarPinnedBridge h c t+(t : ℝ)/(h : ℝ)*(Real.sqrt h*y)) = _
    ring
  change |scalarQueryBridgeComplete h (x,c) t-scalarQueryBridgeComplete h (y,c) t| ≤ _
  rw [he,abs_mul,abs_mul,abs_of_nonneg hr0,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hr1

/-- The actual weighted innovation on the current cell has endpoint slope
at most the actual start coefficient times `sqrt(h)`. The auxiliary path
is held fixed and cancels exactly. -/
theorem currentWeightedDriver_endpoint_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h : ℝ≥0) (hh : 0 < h)
    (c d : ScalarContinuousPath h) (x y : ℝ) :
    let F := shiftedCoefficient (actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ) a
    let G := shiftedCoefficient (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) a
    let hF := continuous_shiftedCoefficient (actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ) a
    let hG := continuous_shiftedCoefficient (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) a
    ‖scalarTwoDriverWeightedPath F G hF hG h (scalarQueryBridgeComplete h (x,c),d)-
      scalarTwoDriverWeightedPath F G hF hG h (scalarQueryBridgeComplete h (y,c),d)‖ ≤
      actualParisiQueryRho W β a*Real.sqrt h*|x-y| := by
  intro F G hF hG
  have hF0 : ∀ t, F t ≤ 0 := by
    intro t
    exact neg_nonpos.mpr (actualParisiQueryRho_bounds W β hβ ((a : ℝ)+t)).1
  have hFstart : -F 0 = actualParisiQueryRho W β a := by
    change -(-actualParisiQueryRho W β ((a : ℝ)+0)) = _
    simp only [add_zero,neg_neg]
  have he : scalarTwoDriverWeightedPath F G hF hG h (scalarQueryBridgeComplete h (x,c),d)-
      scalarTwoDriverWeightedPath F G hF hG h (scalarQueryBridgeComplete h (y,c),d) =
      -(scalarStieltjesWeightedPath F hF h (scalarQueryBridgeComplete h (x,c))-
        scalarStieltjesWeightedPath F hF h (scalarQueryBridgeComplete h (y,c))) := by
    unfold scalarTwoDriverWeightedPath
    abel
  rw [he,norm_neg]
  have hw := weightedPath_nonpos_driver_bound F hF hF0 h
    (scalarQueryBridgeComplete h (x,c)) (scalarQueryBridgeComplete h (y,c))
  rw [hFstart] at hw
  exact hw.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (queryBridge_endpoint_norm_bound h hh c x y) (actualParisiQueryRho_bounds W β hβ a).1)

/-- After the literal fixed-past restart, the current-cell field satisfies
the required endpoint estimate. No future path or terminal spin is revealed. -/
theorem currentCellField_endpoint_bound
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h : ℝ≥0) (hh : 0 < h)
    (B D : ScalarContinuousPath a) (c d : ScalarContinuousPath h)
    (hd : d ⟨0,le_rfl,h.coe_nonneg⟩ = 0) (x y : ℝ) :
    |restartedField W β hβ a h B D (scalarQueryBridgeComplete h (x,c),d)-
      restartedField W β hβ a h B D (scalarQueryBridgeComplete h (y,c),d)| ≤
      (Real.exp h*Real.sqrt h*actualParisiQueryRho W β a)*|x-y| := by
  let b := actualParisiFullScalarDrift β
  let F := actualParisiNegativeRhoStieltjes W β hβ
  let G := actualParisiSigmaStieltjes W β hβ
  let hF := continuous_actualParisiNegativeRhoStieltjes W β hβ
  let hG := continuous_actualParisiSigmaStieltjes W β hβ
  let X := scalarTwoDriverPicardPath b F G hF hG a (0,(B,D)) ⟨a,a.coe_nonneg,le_rfl⟩
  let J := scalarTwoDriverWeightedPath (shiftedCoefficient F hF a) (shiftedCoefficient G hG a)
    (continuous_shiftedCoefficient F hF a) (continuous_shiftedCoefficient G hG a) h
  have he (z : ℝ) : restartedField W β hβ a h B D (scalarQueryBridgeComplete h (z,c),d) =
      scalarForwardPicardPath (SKConstants.BoundedLipschitzDrift.translated b a 0) h
        (X,J (scalarQueryBridgeComplete h (z,c),d)) ⟨h,h.coe_nonneg,le_rfl⟩ :=
    twoDriverPicard_concat_restart b F G hF hG a h h le_rfl 0 B D _ d
      (scalarQueryBridgeComplete_zero h (z,c)) hd
  rw [he x,he y]
  have hw := currentWeightedDriver_endpoint_norm_bound W β hβ a h hh c d x y
  have hE : 0 ≤ actualParisiQueryRho W β a*Real.sqrt h*|x-y| := by
    exact mul_nonneg (mul_nonneg (actualParisiQueryRho_bounds W β hβ a).1
      (Real.sqrt_nonneg _)) (abs_nonneg _)
  have hg := scalarForwardPicardPath_driver_bound
    (SKConstants.BoundedLipschitzDrift.translated b a 0) h
    (X,J (scalarQueryBridgeComplete h (x,c),d))
    (X,J (scalarQueryBridgeComplete h (y,c),d)) _ hE (fun t => by
      rw [add_sub_add_left_eq_sub]
      exact ((J (scalarQueryBridgeComplete h (x,c),d)-
        J (scalarQueryBridgeComplete h (y,c),d)).norm_coe_le_norm t).trans hw)
    ⟨h,h.coe_nonneg,le_rfl⟩
  have hlip : (SKConstants.BoundedLipschitzDrift.translated b a 0).lip = 1 := rfl
  rw [hlip,NNReal.coe_one,one_mul] at hg
  exact hg.trans_eq (by ring)

/-- The current-cell posterior is unit Lipschitz in its final field, so it
inherits the sharp current-cell endpoint bound for every original past. -/
theorem currentCellPosterior_endpoint_bound
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h : ℝ≥0) (hh : 0 < h)
    (B D : ScalarContinuousPath a) (c d : ScalarContinuousPath h)
    (hd : d ⟨0,le_rfl,h.coe_nonneg⟩ = 0) (x y : ℝ) :
    |actualParisiFullMagnetization β (a+h)
        (restartedField W β hβ a h B D (scalarQueryBridgeComplete h (x,c),d))-
      actualParisiFullMagnetization β (a+h)
        (restartedField W β hβ a h B D (scalarQueryBridgeComplete h (y,c),d))| ≤
      (Real.exp h*Real.sqrt h*actualParisiQueryRho W β a)*|x-y| := by
  have hm := (N19.actualParisiFullMagnetization_lipschitz β (a+h)).dist_le_mul
    (restartedField W β hβ a h B D (scalarQueryBridgeComplete h (x,c),d))
    (restartedField W β hβ a h B D (scalarQueryBridgeComplete h (y,c),d))
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hm
  exact hm.trans (currentCellField_endpoint_bound W β hβ a h hh B D c d hd x y)

/-- Concatenation reads the prescribed past before the joining time. -/
theorem concat_eval_le (a h : ℝ≥0) (B : ScalarContinuousPath a)
    (p : ScalarContinuousPath h) (t : Icc (0 : ℝ) ((a+h : ℝ≥0) : ℝ))
    (ht : (t : ℝ) ≤ a) :
    scalarConcatPath a h (B,p) t = B ⟨t,t.property.1,ht⟩ := by
  simp only [scalarConcatPath,ContinuousMap.coe_mk,projIcc_of_mem _ ⟨t.property.1,ht⟩,
    projIcc_of_le_left h.coe_nonneg (sub_nonpos.mpr ht)]
  ring

/-- Concatenation reads the prescribed future increments after the join. -/
theorem concat_eval_ge (a h : ℝ≥0) (B : ScalarContinuousPath a)
    (p : ScalarContinuousPath h) (t : Icc (0 : ℝ) ((a+h : ℝ≥0) : ℝ))
    (ht : (a : ℝ) ≤ t) :
    scalarConcatPath a h (B,p) t = B ⟨a,a.coe_nonneg,le_rfl⟩+
      p ⟨(t : ℝ)-a,sub_nonneg.mpr ht,by
        have H := t.property.2
        simp only [NNReal.coe_add] at H
        linarith⟩-p ⟨0,le_rfl,h.coe_nonneg⟩ := by
  simp [scalarConcatPath,projIcc_of_right_le a.coe_nonneg ht,projIcc_of_mem,
    show 0 ≤ (t : ℝ)-(a : ℝ) by linarith,
    show (t : ℝ)-(a : ℝ) ≤ h by
      have H := t.property.2
      simp only [NNReal.coe_add] at H
      linarith]

/-- The literal continuous-path concatenation is associative, with the
necessary exact horizon cast retained. Nonzero-based paths are allowed. -/
theorem concat_assoc (a h f : ℝ≥0) (B : ScalarContinuousPath a)
    (p : ScalarContinuousPath h) (q : ScalarContinuousPath f) :
    scalarPathHorizonCast (add_assoc a h f)
      (scalarConcatPath a (h+f) (B,scalarConcatPath h f (p,q))) =
      scalarConcatPath (a+h) f (scalarConcatPath a h (B,p),q) := by
  ext t
  rw [scalarPathHorizonCast_eval]
  by_cases hta : (t : ℝ) ≤ a
  · rw [concat_eval_le _ _ _ _ _ hta,
      concat_eval_le _ _ _ _ _ (by simp only [NNReal.coe_add]; linarith [h.coe_nonneg]),
      concat_eval_le _ _ _ _ _ hta]
  · have hat : (a : ℝ) ≤ t := le_of_not_ge hta
    rw [concat_eval_ge _ _ _ _ _ hat]
    by_cases htah : (t : ℝ) ≤ (a+h : ℝ≥0)
    · rw [concat_eval_le _ _ _ _ _ (by
        simp only [NNReal.coe_add] at htah
        dsimp
        linarith),
        concat_eval_le _ _ _ _ _ (by dsimp; exact h.coe_nonneg),
        concat_eval_le _ _ _ _ _ htah,
        concat_eval_ge _ _ _ _ _ hat]
    · have haht : ((a+h : ℝ≥0) : ℝ) ≤ t := le_of_not_ge htah
      rw [concat_eval_ge _ _ _ _ _ (by
        simp only [NNReal.coe_add] at haht
        dsimp
        linarith),
        concat_eval_le _ _ _ _ _ (by dsimp; exact h.coe_nonneg),
        concat_eval_ge _ _ _ _ _ haht,
        concat_eval_ge _ _ _ _ _ (by
          simp only [NNReal.coe_add]
          exact le_add_of_nonneg_right h.coe_nonneg)]
      simp only [NNReal.coe_add,Subtype.coe_mk,add_sub_cancel_left,sub_sub]
      ring

/-- Horizon casts commute with the literal two-driver Picard construction. -/
theorem picard_horizon_cast (b : BoundedLipschitzDrift)
    (F G : StieltjesFunction ℝ) (hF : Continuous F) (hG : Continuous G)
    {S T : ℝ≥0} (e : S = T) (z : ℝ) (B D : ScalarContinuousPath T) :
    scalarTwoDriverPicardPath b F G hF hG S
      (z,(scalarPathHorizonCast e B,scalarPathHorizonCast e D)) =
      scalarPathHorizonCast e (scalarTwoDriverPicardPath b F G hF hG T (z,(B,D))) := by
  cases e
  rfl

/-- Joining the current cell and then the future gives exactly the same
actual terminal field as the original fresh-seed callback. -/
theorem freshField_eq_current_restart
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a)
    (c d : ScalarContinuousPath h) (b e : ScalarContinuousPath f) (x : ℝ) :
    freshRowTerminalField W β hβ a h f B D
      (x,(c,(b,(scalarConcatPath h f (d,e),0)))) =
    restartedField W β hβ (a+h) f
      (scalarConcatPath a h (B,scalarQueryBridgeComplete h (x,c)))
      (scalarConcatPath a h (D,d)) (b,e) := by
  have hb := concat_assoc a h f B (scalarQueryBridgeComplete h (x,c)) b
  have hd := concat_assoc a h f D d e
  unfold restartedField
  rw [← hb,← hd,picard_horizon_cast,scalarPathHorizonCast_eval]
  unfold freshRowTerminalField freshRowDrivers
  congr 1
  apply Subtype.ext
  simp only [NNReal.coe_add,Subtype.coe_mk,add_assoc]

/-- A measurable actual magnetization observable is integrable against
every finite measure, by its proved uniform bound one. -/
theorem magnetization_comp_integrable {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (β t : ℝ) (Y : A → ℝ) (hY : Measurable Y) :
    Integrable (fun u => actualParisiFullMagnetization β t (Y u)) μ := by
  apply Integrable.of_bound
    (((N19.actualParisiFullMagnetization_lipschitz β t).continuous.measurable).comp
      hY).aestronglyMeasurable 1
  exact ae_of_all _ fun u => by
    simpa only [Real.norm_eq_abs,Function.comp_apply] using
      (actualParisiFullMagnetization_curvature_bounds β t (Y u)).1

/-- At each fixed current bridge, integrate the two genuine future Wiener
paths first. The actual posterior restart removes the whole remaining
horizon, leaving only the current-cell posterior averaged over its D path. -/
theorem freshFutureAverage_eq_currentPosterior
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a)
    (c : ScalarContinuousPath h) (x : ℝ) :
    (∫ b, ∫ d, actualParisiFullMagnetization β (a+(h+f))
      (freshRowTerminalField W β hβ a h f B D (x,(c,(b,(d,0)))))
      ∂scalarPrimitiveBrownianPathLaw W (h+f) ∂scalarPrimitiveBrownianPathLaw W f) =
    ∫ d, actualParisiFullMagnetization β (a+h)
      (restartedField W β hβ a h B D (scalarQueryBridgeComplete h (x,c),d))
      ∂scalarPrimitiveBrownianPathLaw W h := by
  let P := fun t => scalarPrimitiveBrownianPathLaw W t
  let H := fun (b : ScalarContinuousPath f) (d : ScalarContinuousPath (h+f)) =>
    actualParisiFullMagnetization β (a+(h+f))
      (freshRowTerminalField W β hβ a h f B D (x,(c,(b,(d,0)))))
  have hm : Measurable (actualParisiFullMagnetization β (a+(h+f))) :=
    (N19.actualParisiFullMagnetization_lipschitz β (a+(h+f))).continuous.measurable
  have hH (b : ScalarContinuousPath f) : Measurable (H b) :=
    hm.comp ((measurable_freshRowTerminalField W β hβ a h f B D).comp (by fun_prop))
  have hi {A : Type} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
      (v : A → ScalarContinuousPath f × ScalarContinuousPath (h+f)) (hv : Measurable v) :
      Integrable (fun u => H (v u).1 (v u).2) μ := by
    apply magnetization_comp_integrable μ β (a+(h+f))
    exact (measurable_freshRowTerminalField W β hβ a h f B D).comp
      (by fun_prop)
  have hsplit (b : ScalarContinuousPath f) :
      (∫ d, H b d ∂P (h+f)) =
      ∫ d, ∫ e, H b (scalarConcatPath h f (d,e)) ∂P f ∂P h := by
    rw [show P (h+f) = ((P h).prod (P f)).map (scalarConcatPath h f) from
      (scalarBrownianConcat_law W h f).symm]
    rw [integral_map (measurable_scalarConcatPath h f).aemeasurable (hH b).aestronglyMeasurable]
    have hI : Integrable
        (fun u : ScalarContinuousPath h × ScalarContinuousPath f => H b (scalarConcatPath h f u))
        ((P h).prod (P f)) :=
      hi ((P h).prod (P f)) (fun u => (b,scalarConcatPath h f u))
        (measurable_const.prodMk (measurable_scalarConcatPath h f))
    exact integral_prod (fun u => H b (scalarConcatPath h f u)) hI
  have hi3 : Integrable
      (fun u : (ScalarContinuousPath f × ScalarContinuousPath h) × ScalarContinuousPath f =>
        H u.1.1 (scalarConcatPath h f (u.1.2,u.2))) (((P f).prod (P h)).prod (P f)) :=
    hi (((P f).prod (P h)).prod (P f))
      (fun u => (u.1.1,scalarConcatPath h f (u.1.2,u.2)))
      (measurable_fst.fst.prodMk ((measurable_scalarConcatPath h f).comp
      (measurable_fst.snd.prodMk measurable_snd)))
  change (∫ b, ∫ d, H b d ∂P (h+f) ∂P f) = _
  calc
    _ = ∫ b, ∫ d, ∫ e, H b (scalarConcatPath h f (d,e)) ∂P f ∂P h ∂P f :=
      integral_congr_ae (ae_of_all _ hsplit)
    _ = ∫ d, ∫ b, ∫ e, H b (scalarConcatPath h f (d,e)) ∂P f ∂P f ∂P h :=
      integral_integral_swap hi3.integral_prod_left
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro d
      change (∫ b, ∫ e, H b (scalarConcatPath h f (d,e)) ∂P f ∂P f) =
        actualParisiFullMagnetization β (a+h)
          (restartedField W β hβ a h B D (scalarQueryBridgeComplete h (x,c),d))
      have he (b e : ScalarContinuousPath f) : H b (scalarConcatPath h f (d,e)) =
          actualParisiFullMagnetization β ((a+h)+f)
            (restartedField W β hβ (a+h) f
              (scalarConcatPath a h (B,scalarQueryBridgeComplete h (x,c)))
              (scalarConcatPath a h (D,d)) (b,e)) := by
        dsimp only [H]
        rw [freshField_eq_current_restart]
        simp only [NNReal.coe_add,add_assoc]
      have hreplace : (∫ b, ∫ e, H b (scalarConcatPath h f (d,e)) ∂P f ∂P f) =
          ∫ b, ∫ e, actualParisiFullMagnetization β ((a+h)+f)
            (restartedField W β hβ (a+h) f
              (scalarConcatPath a h (B,scalarQueryBridgeComplete h (x,c)))
              (scalarConcatPath a h (D,d)) (b,e)) ∂P f ∂P f := by
        apply integral_congr_ae
        apply ae_of_all
        intro b
        exact integral_congr_ae (ae_of_all _ fun e => he b e)
      rw [hreplace]
      rw [← integral_prod _ (magnetization_comp_integrable _ β ((a+h)+f) _
        (measurable_restartedField W β hβ (a+h) f _ _))]
      exact wiener_restarted_magnetization_mean W β hβ (a+h) f _ _

/-- Exact deterministic-start future elimination for the original
endpoint-averaged callback, at every original continuous B/D past. -/
theorem freshEndpointMean_eq_currentPosterior_integral
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a) (x : ℝ) :
    freshEndpointMean W β hβ a h f B D x =
      ∫ c, ∫ d, actualParisiFullMagnetization β (a+h)
        (restartedField W β hβ a h B D (scalarQueryBridgeComplete h (x,c),d))
        ∂scalarPrimitiveBrownianPathLaw W h ∂scalarPrimitiveBridgePathLaw W h := by
  rw [freshEndpointMean_eq_posterior_integral]
  exact integral_congr_ae (ae_of_all _ fun c =>
    freshFutureAverage_eq_currentPosterior W β hβ a h f B D c x)

/-- The actual endpoint-averaged sign is independent of how far the
experiment continues after the current cell. -/
theorem freshEndpointMean_future_independent
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f g : ℝ≥0) (B D : ScalarContinuousPath a) (x : ℝ) :
    freshEndpointMean W β hβ a h f B D x = freshEndpointMean W β hβ a h g B D x := by
  rw [freshEndpointMean_eq_currentPosterior_integral,
    freshEndpointMean_eq_currentPosterior_integral]

/-- Integrating the current-cell estimate after the proved future restart
gives the required endpoint Lipschitz constant, for every positive duration.
The short-cell assumption is needed only by the later schedule comparison. -/
theorem freshEndpointMean_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (hh : 0 < h) (B D : ScalarContinuousPath a) :
    LipschitzWith (Real.toNNReal (Real.exp h*Real.sqrt h*actualParisiQueryRho W β a))
      (freshEndpointMean W β hβ a h f B D) := by
  let μ := (scalarPrimitiveBridgePathLaw W h).prod (scalarPrimitiveBrownianPathLaw W h)
  let L := Real.exp h*Real.sqrt h*actualParisiQueryRho W β a
  let Y := fun (x : ℝ) (u : ScalarContinuousPath h × ScalarContinuousPath h) =>
    restartedField W β hβ a h B D (scalarQueryBridgeComplete h (x,u.1),u.2)
  let M := fun (x : ℝ) (u : ScalarContinuousPath h × ScalarContinuousPath h) =>
    actualParisiFullMagnetization β (a+h) (Y x u)
  have hY (x : ℝ) : Measurable (Y x) :=
    (measurable_restartedField W β hβ a h B D).comp
      (((measurable_scalarQueryBridgeComplete h).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have hM (x : ℝ) : Integrable (M x) μ :=
    magnetization_comp_integrable μ β (a+h) (Y x) (hY x)
  have he (x : ℝ) : freshEndpointMean W β hβ a h f B D x = ∫ u, M x u ∂μ := by
    rw [freshEndpointMean_eq_currentPosterior_integral]
    exact (integral_prod (M x) (hM x)).symm
  have hL : 0 ≤ L :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
      (actualParisiQueryRho_bounds W β hβ a).1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq,he x,he y,← integral_sub (hM x) (hM y)]
  change |∫ u, M x u-M y u ∂μ| ≤ (Real.toNNReal L : ℝ)*|x-y|
  rw [Real.coe_toNNReal _ hL,← Real.norm_eq_abs]
  have hb : ∀ᵐ u ∂μ, ‖M x u-M y u‖ ≤ L*|x-y| := by
    filter_upwards [(measurePreserving_snd (μ := scalarPrimitiveBridgePathLaw W h)
      (ν := scalarPrimitiveBrownianPathLaw W h)).quasiMeasurePreserving.ae
        (scalarPrimitiveBrownianPathLaw_zero_ae W h)] with u hu
    simpa only [M,Y,Real.norm_eq_abs,L] using
      currentCellPosterior_endpoint_bound W β hβ a h hh B D u.1 u.2 hu x y
  have hn := norm_integral_le_of_norm_le_const hb
  simpa only [μ,probReal_univ,mul_one] using hn

/-- The exact remaining N9Z2 scalar node, with no unproved hypotheses. -/
theorem freshEndpointLipschitzStatement_holds : FreshEndpointLipschitzStatement := by
  intro Ω _ W β hβ a h f hh _ B D
  exact freshEndpointMean_lipschitz W β hβ a h f hh B D

/-- N9-Z follows by the existing unchanged schedule/envelope reduction. -/
theorem fineMixedEnvelopeStatement_holds : Blueprint5.FineMixedEnvelopeStatement :=
  N9Z2.fineMixedEnvelopeStatement_holds freshEndpointLipschitzStatement_holds

end SKConstants.Completion.L1
