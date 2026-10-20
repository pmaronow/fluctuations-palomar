module

public import SKBarriers2.Corner.Evenness
public import OAI.Probability.SKBarriers.Gaussian.GaussianMassDerivative
public import OAI.Probability.SKBarriers.Calculus.ParameterStepDerivative
public import OAI.Probability.SKBarriers.Calculus.ParameterFieldMap
public import OAI.Probability.SKBarriers.Calculus.ParameterRecursion
public import OAI.Probability.SKBarriers.Scalar.VectorAverageAlgebra

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2.Corner

section General
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def massStepDerivative (m : ℝ) (v : E) (f : E → ℝ) (x : E) : ℝ :=
  (vectorStepAverage m v f f x - vectorStep m v f x) / m

theorem vectorStep_hasDerivAt_mass {f : E → ℝ} (hf : BoundedDerivs f)
    {m : ℝ} (hm : m ≠ 0) (v x : E) :
    HasDerivAt (fun a => vectorStep a v f x) (massStepDerivative m v f x) m := by
  exact gaussianStep_hasDerivAt_mass_ne_zero (hf.compCLM (vectorTranslation v)) x hm

def MovingMassRegular (a d : ℝ) (F : ℝ × E → ℝ) : Prop :=
  ParamRegular F ∧ ParamRegular (fun z => (a + z.1 * d) * F z)

private theorem param_slice_hasDerivAt {F : ℝ × E → ℝ} (hF : Differentiable ℝ F)
    (lam : ℝ) (x : E) :
    HasDerivAt (fun t => F (t,x)) (fderiv ℝ F (lam,x) (1,0)) lam := by
  have h := (hF (lam,x)).hasFDerivAt.comp_hasDerivAt lam
    ((hasDerivAt_id lam).prodMk (hasDerivAt_const lam x))
  simpa only [one_smul, Function.comp_def, id_eq] using h

theorem vectorStep_hasDerivAt_moving_mass {F : ℝ × E → ℝ} {a d lam : ℝ}
    (hF : MovingMassRegular a d F) (hm : a + lam * d ≠ 0)
    (v x : E) :
    HasDerivAt (fun t => vectorStep (a + t * d) v (fun y => F (t,y)) x)
      (d * massStepDerivative (a + lam * d) v (fun y => F (lam,y)) x +
        vectorStepAverage (a + lam * d) v (fun y => F (lam,y))
          (fun y => fderiv ℝ F (lam,y) (1,0)) x) lam := by
  let m : ℝ → ℝ := fun t => a + t * d
  let W : ℝ × E → ℝ := fun z => m z.1 * F z
  let Z : ℝ × E → ℝ := fun z => vectorStep 1 v (fun y => W (z.1,y)) z.2
  have hW : ParamRegular (fun z : ℝ × (E × ℝ) => W (z.1, z.2.1 + z.2.2 • v)) :=
    hF.2.fieldComp (vectorTranslation v)
  have hZ : ParamRegular Z := hW.gaussianStep 1
  have hdZ := param_slice_hasDerivAt (hZ.1.differentiable (by norm_num)) lam x
  have hZder := hW.parameterDerivative_gaussianStep 1 (lam,x) 1
  change fderiv ℝ Z (lam,x) (1,0) = _ at hZder
  have hpoint (y : ℝ) :
      fderiv ℝ (fun z : ℝ × (E × ℝ) => W (z.1,z.2.1+z.2.2 • v))
        (lam,(x,y)) (1,0) =
      d * F (lam,x+y • v) + m lam * fderiv ℝ F (lam,x+y • v) (1,0) := by
    have hcomp := (param_slice_hasDerivAt (hF.1.1.differentiable (by norm_num))
      lam (x+y • v))
    have hw := (((hasDerivAt_id lam).mul_const d).const_add a).mul hcomp
    have hj := param_slice_hasDerivAt
      (hW.1.differentiable (by norm_num)) lam (x,y)
    apply hj.unique
    simpa only [W, m, Pi.mul_def, one_mul, id_eq] using hw
  change fderiv ℝ Z (lam,x) (1,0) =
    ∫ y, fderiv ℝ (fun z : ℝ × (E × ℝ) => W (z.1,z.2.1+z.2.2 • v))
      (lam,(x,y)) (1,0)
      ∂gaussianStepLaw 1 (fun z : (ℝ × E) × ℝ => W (z.1.1,z.1.2+z.2 • v)) (lam,x) at hZder
  simp_rw [hpoint] at hZder
  have heq (t : ℝ) (ht : m t ≠ 0) :
      vectorStep (m t) v (fun y => F (t,y)) x = Z (t,x) / m t := by
    simp only [vectorStep, gaussianStep, ht, ite_false, positiveGaussianLogStep,
      Z, W, m, one_mul, one_ne_zero, div_one]
  have he : (fun t => vectorStep (m t) v (fun y => F (t,y)) x) =ᶠ[𝓝 lam]
      (fun t => Z (t,x) / m t) := by
    have hmc : Continuous m := continuous_const.add (continuous_id.mul continuous_const)
    filter_upwards [hmc.continuousAt.eventually (eventually_ne_nhds hm)] with t ht
    exact heq t ht
  have hd := hdZ.div (((hasDerivAt_id lam).mul_const d).const_add a) hm
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  rw [hZder]
  have hlaw : gaussianStepLaw 1
      (fun z : (ℝ × E) × ℝ => W (z.1.1,z.1.2+z.2 • v)) (lam,x) =
      gaussianStepLaw (m lam) (fun z : E × ℝ => F (lam,z.1+z.2 • v)) x := by
    simp only [gaussianStepLaw, W, one_mul]
  simp only [one_mul, id_eq]
  rw [show Z (lam,x) = m lam * vectorStep (m lam) v (fun y => F (lam,y)) x by
    rw [heq lam hm]; field_simp [show m lam ≠ 0 from hm]]
  rw [hlaw]
  have hft := hF.1.fieldComp (vectorTranslation v)
  have hfI := (hF.1.2.1.expGrowth.fieldComp (vectorTranslation v)).integrable_paramStepLaw
    hft hft.1.continuous (m lam) (lam,x)
  have hgE : ParamExpGrowth (fun z : ℝ × E => fderiv ℝ F z (1,0)) := by
    apply hF.1.2.2.1.of_norm_le (K := ‖((1 : ℝ),(0 : E))‖) (norm_nonneg _)
    intro z
    exact (fderiv ℝ F z).le_opNorm _ |>.trans_eq (mul_comm _ _)
  have hgc : Continuous (fun z : ℝ × E => fderiv ℝ F z (1,0)) :=
    (hF.1.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgI := (hgE.fieldComp (vectorTranslation v)).integrable_paramStepLaw hft
    (hgc.comp (continuous_fst.prodMk
      (continuous_snd.fst.add (continuous_snd.snd.smul continuous_const)))) (m lam) (lam,x)
  change Integrable (fun y => F (lam,x+y • v))
    (gaussianStepLaw (m lam) (fun z : E × ℝ => F (lam,z.1+z.2 • v)) x) at hfI
  change Integrable (fun y => fderiv ℝ F (lam,x+y • v) (1,0))
    (gaussianStepLaw (m lam) (fun z : E × ℝ => F (lam,z.1+z.2 • v)) x) at hgI
  rw [integral_add (hfI.const_mul d) (hgI.const_mul (m lam)),
    integral_const_mul, integral_const_mul]
  simp only [massStepDerivative, vectorStepAverage, gaussianAverage]
  dsimp only [m]
  field_simp [hm]
  ring_nf
  have hm' : d * lam + a ≠ 0 := by simpa only [mul_comm, add_comm] using hm
  field_simp [hm']
  ring

theorem vectorStep_moving_mass_contDiffAt {F : ℝ × E → ℝ} {a d lam : ℝ}
    (hF : MovingMassRegular a d F) (hm : a + lam * d ≠ 0)
    (v x : E) :
    ContDiffAt ℝ 2 (fun t => vectorStep (a + t * d) v (fun y => F (t,y)) x) lam := by
  let W : ℝ × E → ℝ := fun z => (a + z.1 * d) * F z
  let Z : ℝ × E → ℝ := fun z => vectorStep 1 v (fun y => W (z.1,y)) z.2
  have hW : ParamRegular (fun z : ℝ × (E × ℝ) => W (z.1,z.2.1+z.2.2 • v)) :=
    hF.2.fieldComp (vectorTranslation v)
  have hZ : ParamRegular Z := hW.gaussianStep 1
  have hc : ContDiff ℝ 2 (fun t => Z (t,x)) := hZ.1.comp (contDiff_id.prodMk contDiff_const)
  have hq : ContDiffAt ℝ 2 (fun t => Z (t,x) / (a+t*d)) lam :=
    hc.contDiffAt.div (contDiff_const.add (contDiff_id.mul contDiff_const)).contDiffAt hm
  have he : (fun t => vectorStep (a+t*d) v (fun y => F (t,y)) x) =ᶠ[𝓝 lam]
      (fun t => Z (t,x) / (a+t*d)) := by
    have hmc : Continuous (fun t : ℝ => a+t*d) :=
      continuous_const.add (continuous_id.mul continuous_const)
    filter_upwards [hmc.continuousAt.eventually (eventually_ne_nhds hm)] with t ht
    simp only [vectorStep, gaussianStep, ht, ite_false, positiveGaussianLogStep,
      Z, W, one_mul, one_ne_zero, div_one]
  exact hq.congr_of_eventuallyEq he

abbrev MassPathEntry (E : Type) := ℝ × ℝ × E

def massPath (l : List (MassPathEntry E)) (lam : ℝ) : List (ℝ × E) :=
  l.map (fun q => (q.1 + lam * q.2.1, q.2.2))

def massPathValue (l : List (MassPathEntry E)) (f : E → ℝ) (z : ℝ × E) : ℝ :=
  vectorIncrementChain (massPath l z.1) f z.2

def MassPathRegular : List (MassPathEntry E) → (E → ℝ) → Prop
  | [], _ => True
  | q::l, f => MovingMassRegular q.1 q.2.1 (massPathValue l f) ∧ MassPathRegular l f

def massPathDerivative : List (MassPathEntry E) → (E → ℝ) → ℝ → E → ℝ
  | [], _, _, _ => 0
  | q::l, f, lam, x =>
    q.2.1 * massStepDerivative (q.1+lam*q.2.1) q.2.2
      (vectorIncrementChain (massPath l lam) f) x +
    vectorStepAverage (q.1+lam*q.2.1) q.2.2
      (vectorIncrementChain (massPath l lam) f) (massPathDerivative l f lam) x

theorem massPath_hasDerivAt (l : List (MassPathEntry E)) (f : E → ℝ)
    (hR : MassPathRegular l f) {lam : ℝ}
    (hm : ∀ q ∈ l, q.1+lam*q.2.1 ≠ 0) (x : E) :
    HasDerivAt (fun t => massPathValue l f (t,x)) (massPathDerivative l f lam x) lam := by
  induction l generalizing x with
  | nil => exact hasDerivAt_const lam (f x)
  | cons q l ih =>
    have hd := vectorStep_hasDerivAt_moving_mass hR.1 (hm q (List.mem_cons_self)) q.2.2 x
    have he : (fun y => fderiv ℝ (massPathValue l f) (lam,y) (1,0)) =
        massPathDerivative l f lam := by
      funext y
      exact (param_slice_hasDerivAt (hR.1.1.1.differentiable (by norm_num)) lam y).unique
        (ih hR.2 (fun p hp => hm p (List.mem_cons_of_mem q hp)) y)
    rw [he] at hd
    exact hd

theorem massPathValue_contDiffAt (l : List (MassPathEntry E)) (f : E → ℝ)
    (hR : MassPathRegular l f) {lam : ℝ}
    (hm : ∀ q ∈ l, q.1+lam*q.2.1 ≠ 0) (x : E) :
    ContDiffAt ℝ 2 (fun t => massPathValue l f (t,x)) lam := by
  cases l with
  | nil =>
    change ContDiffAt ℝ 2 (fun _ : ℝ => f x) lam
    exact contDiffAt_const
  | cons q l =>
    exact vectorStep_moving_mass_contDiffAt hR.1 (hm q List.mem_cons_self) q.2.2 x

theorem massPath_sub_eq_integral (l : List (MassPathEntry E)) (f : E → ℝ)
    (hR : MassPathRegular l f)
    (hm : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ q ∈ l, q.1+lam*q.2.1 ≠ 0) (x : E) :
    massPathValue l f (1,x) - massPathValue l f (0,x) =
      ∫ lam in (0 : ℝ)..1, massPathDerivative l f lam x := by
  have hcont : ContinuousOn (fun lam => massPathDerivative l f lam x) (Icc (0 : ℝ) 1) := by
    have hdcont : ContinuousOn (deriv (fun t => massPathValue l f (t,x))) (Icc (0 : ℝ) 1) := by
      intro lam hlam
      exact ((massPathValue_contDiffAt l f hR (hm lam hlam) x).derivWithin
        (m := 0) (by norm_num)).continuousAt.continuousWithinAt
    apply hdcont.congr
    intro lam hlam
    exact (massPath_hasDerivAt l f hR (hm lam hlam) x).deriv.symm
  have hi : IntervalIntegrable (fun lam => massPathDerivative l f lam x) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using hcont)
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun lam hlam => massPath_hasDerivAt l f hR
      (hm lam (by simpa only [uIcc_of_le zero_le_one] using hlam)) x)
    hi

theorem massStepDerivative_regular {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v : E) :
    Continuous (massStepDerivative m v f) ∧ HasExpGrowth (massStepDerivative m v f) := by
  have ha := vectorIncrementAverage_regular [(m,v)] hf hf.1.continuous hf.hasExpGrowth
  change Continuous (vectorStepAverage m v f f) ∧ HasExpGrowth (vectorStepAverage m v f f) at ha
  have hs := vectorStep_regular hf m v
  refine ⟨(ha.1.sub hs.1.continuous).div_const m, ?_⟩
  change HasExpGrowth (fun x => (vectorStepAverage m v f f x - vectorStep m v f x) / m)
  simpa only [div_eq_mul_inv, sub_eq_add_neg, neg_one_mul] using
    (ha.2.add ((HasExpGrowth.const (-1)).mul hs.hasExpGrowth)).mul (HasExpGrowth.const m⁻¹)

def massPathSensitivity (l : List (MassPathEntry E)) (f : E → ℝ) (lam : ℝ)
    (j : Fin l.length) : E → ℝ :=
  vectorIncrementAverage (massPath (l.take j.val) lam)
    (vectorIncrementChain (massPath (l.drop j.val) lam) f)
    (massStepDerivative ((l.get j).1+lam*(l.get j).2.1) (l.get j).2.2
      (vectorIncrementChain (massPath (l.drop (j.val+1)) lam) f))

theorem massPathSensitivity_regular (l : List (MassPathEntry E)) {f : E → ℝ}
    (hf : BoundedDerivs f) (lam : ℝ) (j : Fin l.length) :
    Continuous (massPathSensitivity l f lam j) ∧ HasExpGrowth (massPathSensitivity l f lam j) := by
  have hS := massStepDerivative_regular
    (vectorIncrementChain_regular (massPath (l.drop (j.val+1)) lam) hf)
    ((l.get j).1+lam*(l.get j).2.1) (l.get j).2.2
  exact vectorIncrementAverage_regular _ (vectorIncrementChain_regular _ hf) hS.1 hS.2

private theorem massPathSensitivity_zero (q : MassPathEntry E) (l : List (MassPathEntry E))
    (f : E → ℝ) (lam : ℝ) :
    massPathSensitivity (q::l) f lam 0 =
      massStepDerivative (q.1+lam*q.2.1) q.2.2 (vectorIncrementChain (massPath l lam) f) := by
  rfl

private theorem massPathSensitivity_succ (q : MassPathEntry E) (l : List (MassPathEntry E))
    (f : E → ℝ) (lam : ℝ) (j : Fin l.length) :
    massPathSensitivity (q::l) f lam j.succ =
      vectorStepAverage (q.1+lam*q.2.1) q.2.2 (vectorIncrementChain (massPath l lam) f)
        (massPathSensitivity l f lam j) := by
  have he : vectorIncrementChain (massPath (l.take j.val) lam)
      (vectorIncrementChain (massPath (l.drop j.val) lam) f) =
      vectorIncrementChain (massPath l lam) f := by
    rw [← vectorIncrementChain_append]
    simp only [massPath, ← List.map_append, List.take_append_drop]
  simp only [massPathSensitivity, Fin.val_succ, List.take_succ_cons, List.drop_succ_cons,
    massPath, List.map_cons, vectorIncrementAverage]
  exact congrArg (fun g => vectorStepAverage (q.1+lam*q.2.1) q.2.2 g
    (massPathSensitivity l f lam j)) he

private theorem vectorStepAverage_fin_sum {f : E → ℝ} (hf : BoundedDerivs f)
    {n : ℕ} (g : Fin n → E → ℝ) (hc : ∀ i, Continuous (g i))
    (hg : ∀ i, HasExpGrowth (g i)) (m : ℝ) (v x : E) :
    vectorStepAverage m v f (fun y => ∑ i, g i y) x =
      ∑ i, vectorStepAverage m v f (g i) x := by
  exact integral_finsetSum Finset.univ (fun i _ =>
    ((hg i).compCLM (vectorTranslation v)).integrable_gaussianStepLaw
      (hf.compCLM (vectorTranslation v)) ((hc i).comp (vectorTranslation v).continuous) m x)

theorem massPathDerivative_eq_sum (l : List (MassPathEntry E)) {f : E → ℝ}
    (hf : BoundedDerivs f) (lam : ℝ) (x : E) :
    massPathDerivative l f lam x =
      ∑ j : Fin l.length, (l.get j).2.1 * massPathSensitivity l f lam j x := by
  induction l generalizing x with
  | nil => simp only [massPathDerivative, List.length_nil, Fin.sum_univ_zero]
  | cons q l ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero, massPathSensitivity_zero,
      massPathSensitivity_succ, massPathDerivative]
    congr 1
    have he : massPathDerivative l f lam =
        fun y => ∑ j : Fin l.length, (l.get j).2.1 * massPathSensitivity l f lam j y :=
      funext ih
    rw [he, vectorStepAverage_fin_sum (vectorIncrementChain_regular _ hf)
      (fun j y => (l.get j).2.1 * massPathSensitivity l f lam j y)
      (fun j => (massPathSensitivity_regular l hf lam j).1.const_mul _)
      (fun j => (HasExpGrowth.const (l.get j).2.1).mul
        (massPathSensitivity_regular l hf lam j).2)]
    exact Finset.sum_congr rfl (fun j _ => congrFun
      (vectorStepAverage_const_mul _ _ _ _ _) x)

theorem massPath_sub_eq_integral_sum (l : List (MassPathEntry E)) {f : E → ℝ}
    (hf : BoundedDerivs f) (hR : MassPathRegular l f)
    (hm : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ q ∈ l, q.1+lam*q.2.1 ≠ 0) (x : E) :
    massPathValue l f (1,x) - massPathValue l f (0,x) =
      ∫ lam in (0 : ℝ)..1,
        ∑ j : Fin l.length, (l.get j).2.1 * massPathSensitivity l f lam j x := by
  rw [massPath_sub_eq_integral l f hR hm x]
  congr 1
  funext lam
  exact massPathDerivative_eq_sum l hf lam x

end General

def windowMassSamples (p s h k : ℝ) (N : ℕ) : List (ℝ × ℝ × (Fin 3 → ℝ)) :=
  let grid := fun (a len c : ℝ) (vs : List (Fin 3 → ℝ)) =>
    (List.range N).flatMap fun j => vs.map fun v =>
      (s+h*(a+len*(j:ℝ)/(N:ℝ)), c, Real.sqrt (h*len/(N:ℝ)) • v)
  let ell := 4*k^2*SKOptimized.Overshoot.varianceCoefficient p
  let repair := fun (vs : List (Fin 3 → ℝ)) =>
    (List.range N).flatMap fun j => vs.map fun v =>
      (s+h*(2+ell*(j:ℝ)/(N:ℝ)), (1:ℝ),
        (k*Real.sqrt (h*(4*SKOptimized.Overshoot.varianceCoefficient p)/(N:ℝ))) • v)
  grid 0 1 3 [SKOptimized.Overshoot.commonVector p k] ++
    grid 1 p 2 [SKOptimized.Overshoot.sharedVector p k] ++
    grid 1 p 1 [SKOptimized.Overshoot.rampVector p k] ++
    grid (1+p) (1-p) 1 [SKOptimized.Overshoot.rampVector p k,
      SKOptimized.Overshoot.postXVector p k, SKOptimized.Overshoot.postYVector p k] ++
    repair [SKOptimized.Overshoot.rampVector p 0,
      (1/Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
      (1/2:ℝ) • SKOptimized.Overshoot.contrast] ++
    grid (2+ell) (2-ell) 1 [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]

theorem window_eq_massSamples (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    OW.window α p s h k N =
      (windowMassSamples p s h k N).map (fun q => (α q.1 / q.2.1, q.2.2)) := by
  simp only [OW.window, windowMassSamples, List.map_append, List.map_flatMap,
    List.map_map, Function.comp_def]

def windowMassPath (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    List (MassPathEntry (Fin 3 → ℝ)) :=
  (windowMassSamples p s h k N).map
    (fun q => (a/q.2.1, (α q.1-a)/q.2.1, β • q.2.2))

theorem windowMassPath_length (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    (windowMassPath β α a p s h k N).length = 12*N := by
  simp [windowMassPath, windowMassSamples, List.length_flatMap]
  omega

theorem massPath_window_eq (β : ℝ) (α : ℝ → ℝ) (a lam p s h k : ℝ) (N : ℕ) :
    massPath (windowMassPath β α a p s h k N) lam =
      (OW.window (interpolatedProfile α a lam) p s h k N).map
        (fun q => (q.1,β • q.2)) := by
  rw [window_eq_massSamples]
  simp only [massPath, windowMassPath, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro q _
  apply Prod.ext
  · dsimp only [interpolatedProfile]
    ring
  · rfl

def massVariationTerminal (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, Phi β α (s+4*h) (x i)

theorem massVariationTerminal_regular (β : ℝ) (α : ℝ → ℝ) (s h : ℝ)
    (hPhi : BoundedDerivs (Phi β α (s+4*h))) :
    BoundedDerivs (massVariationTerminal β α s h) := by
  change BoundedDerivs (fun x : Fin 3 → ℝ => ∑ i, Phi β α (s+4*h) (x i))
  simpa [Fin.sum_univ_succ, add_assoc] using
    ((hPhi.compCLM (tripleCoordinate 0)).add
      (hPhi.compCLM (tripleCoordinate 1))).add (hPhi.compCLM (tripleCoordinate 2))

def interpolatedBoundary (β : ℝ) (α : ℝ → ℝ) (a lam p s h k : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  vectorIncrementChain ((OW.window (interpolatedProfile α a lam) p s h k N).map
    (fun q => (q.1,β • q.2))) (massVariationTerminal β α s h) (fun _ => z)

theorem interpolatedBoundary_one (β : ℝ) (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) (z : ℝ) :
    interpolatedBoundary β α a 1 p s h k N z = OW.boundary β α p s h k N z := by
  have he : interpolatedProfile α a 1 = α := by
    funext t
    simp only [interpolatedProfile, one_mul, add_sub_cancel]
  rw [interpolatedBoundary, he]
  rfl

theorem interpolatedBoundary_sub_eq_integral (β : ℝ) (α : ℝ → ℝ)
    (a p s h k : ℝ) (N : ℕ)
    (hf : BoundedDerivs (massVariationTerminal β α s h))
    (hR : MassPathRegular (windowMassPath β α a p s h k N) (massVariationTerminal β α s h))
    (hm : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ q ∈ windowMassPath β α a p s h k N,
      q.1+lam*q.2.1 ≠ 0) (z : ℝ) :
    OW.boundary β α p s h k N z - interpolatedBoundary β α a 0 p s h k N z =
      ∫ lam in (0 : ℝ)..1,
        ∑ j : Fin (windowMassPath β α a p s h k N).length,
          ((windowMassPath β α a p s h k N).get j).2.1 *
            massPathSensitivity (windowMassPath β α a p s h k N)
              (massVariationTerminal β α s h) lam j (fun _ => z) := by
  have H := massPath_sub_eq_integral_sum _ hf hR hm (fun _ => z)
  have he (lam : ℝ) : massPathValue (windowMassPath β α a p s h k N)
      (massVariationTerminal β α s h) (lam,fun _ => z) =
      interpolatedBoundary β α a lam p s h k N z := by
    rw [massPathValue, massPath_window_eq]
    rfl
  rw [he 1, he 0, interpolatedBoundary_one] at H
  exact H

end SKBarriers2.Corner
