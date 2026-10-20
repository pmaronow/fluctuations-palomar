module

public import SKBarriers2.Analysis.ParamStep
public import OAI.Probability.SKBarriers.Calculus.ParameterAverage
public import OAI.Probability.SKBarriers.Replicas.VectorBranch

@[expose] public section

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
open scoped Topology

namespace SKBarriers2.ParamChain

section Composition

variable {P X Y Z : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]

local instance : NormedAddCommGroup (P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (P × X →L[ℝ] P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × X →L[ℝ] P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (P × Y →L[ℝ] P × X) := inferInstance
local instance : NormedSpace ℝ (P × Y →L[ℝ] P × X) := inferInstance
local instance : NormedAddCommGroup (P × Y →L[ℝ] P × Y →L[ℝ] P × X) := inferInstance
local instance : NormedSpace ℝ (P × Y →L[ℝ] P × Y →L[ℝ] P × X) := inferInstance

private theorem affineBilinear_bound (A : Y →L[ℝ] X) (L : P →L[ℝ] Y →L[ℝ] X)
    {R : ℝ} {p : P} (hp : ‖p‖ ≤ R) (y : Y) :
    ‖A y + L p y‖ ≤ (‖A‖ + ‖L‖ * max R 0) * ‖y‖ := by
  have hp' : ‖p‖ ≤ max R 0 := hp.trans (le_max_left _ _)
  calc
    ‖A y + L p y‖ ≤ ‖A y‖ + ‖L p y‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖y‖ + (‖L‖ * ‖p‖) * ‖y‖ :=
      add_le_add (A.le_opNorm y)
        (((L p).le_opNorm y).trans (mul_le_mul_of_nonneg_right (L.le_opNorm p) (norm_nonneg y)))
    _ ≤ (‖A‖ + ‖L‖ * max R 0) * ‖y‖ := by
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp' (norm_nonneg L)) (norm_nonneg y)]

theorem growth_affineBilinear {f : P × X → Z} (hf : ParamExpGrowth f)
    (A : Y →L[ℝ] X) (L : P →L[ℝ] Y →L[ℝ] X) :
    ParamExpGrowth (fun z : P × Y => f (z.1, A z.2 + L z.1 z.2)) := by
  intro R
  obtain ⟨C, M, hC, hM, hbound⟩ := hf R
  refine ⟨C, M * (‖A‖ + ‖L‖ * max R 0), hC, by positivity, ?_⟩
  intro p y hp
  apply (hbound p (A y + L p y) hp).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (affineBilinear_bound A L hp y) hM).trans_eq (by ring)

theorem smooth_affineBilinear {f : P × X → ℝ} (hf : ParamSmooth f)
    (A : Y →L[ℝ] X) (L : P →L[ℝ] Y →L[ℝ] X) :
    ParamSmooth (fun z : P × Y => f (z.1, A z.2 + L z.1 z.2)) := by
  let S : P × Y →L[ℝ] X := A.comp (ContinuousLinearMap.snd ℝ P Y)
  let K : P × Y →L[ℝ] P × X := (ContinuousLinearMap.fst ℝ P Y).prod S
  let J : P × Y →L[ℝ] (P × Y →L[ℝ] P × X) :=
    (ContinuousLinearMap.compL ℝ (P × Y) X (P × X)
      (ContinuousLinearMap.inr ℝ P X)).comp L.deriv₂
  let G : P × Y → P × X := fun z => K z +
    (ContinuousLinearMap.inr ℝ P X) (L z.1 z.2)
  have hGeq (z : P × Y) : G z = (z.1, A z.2 + L z.1 z.2) := by
    change (z.1 + 0, A z.2 + L z.1 z.2) = _
    rw [add_zero]
  have hG : ContDiff ℝ 2 G := K.contDiff.add
    ((ContinuousLinearMap.inr ℝ P X).contDiff.comp L.isBoundedBilinearMap.contDiff)
  have hDG : fderiv ℝ G = fun z => K + J z := by
    funext z
    exact (K.hasFDerivAt.add ((ContinuousLinearMap.inr ℝ P X).hasFDerivAt.comp z
      (L.isBoundedBilinearMap.hasFDerivAt z))).fderiv
  have hDDG : fderiv ℝ (fderiv ℝ G) = fun _ => J := by
    rw [hDG]
    exact funext (fun z => (J.hasFDerivAt.const_add K).fderiv)
  have hDgrow : ParamExpGrowth (fderiv ℝ G) := by
    rw [hDG]
    exact (ParamExpGrowth.of_bounded (norm_nonneg K) (fun _ => le_rfl)).add
      (ParamExpGrowth.continuousLinearMap J)
  have hDDgrow : ParamExpGrowth (fderiv ℝ (fderiv ℝ G)) := by
    rw [hDDG]
    exact ParamExpGrowth.of_bounded (f := fun _ : P × Y => J) (norm_nonneg J) (fun _ => le_rfl)
  let C : P × Y → ℝ := fun z => |f (G z)| + ‖fderiv ℝ f (G z)‖ +
    ‖fderiv ℝ (fderiv ℝ f) (G z)‖
  let D : P × Y → ℝ := fun z => 1 + ‖fderiv ℝ G z‖ + ‖fderiv ℝ (fderiv ℝ G) z‖
  have hg0 : ParamExpGrowth (fun z => f (G z)) := by
    simpa only [hGeq] using growth_affineBilinear hf.2.1 A L
  have hg1 : ParamExpGrowth (fun z => fderiv ℝ f (G z)) := by
    simpa only [hGeq] using growth_affineBilinear hf.2.2.1 A L
  have hg2 : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ f) (G z)) := by
    simpa only [hGeq] using growth_affineBilinear hf.2.2.2 A L
  have hC : ParamExpGrowth C := (hg0.norm.add hg1.norm).add hg2.norm
  have hD : ParamExpGrowth D :=
    ((ParamExpGrowth.of_bounded zero_le_one (fun _ => by norm_num)).add hDgrow.norm).add hDDgrow.norm
  have henv := hC.mul (hD.mul hD)
  have hjet (j : ℕ) (hj : j ≤ 2) (z : P × Y) :
      ‖iteratedFDeriv ℝ j (fun w => f (G w)) z‖ ≤ 2 * (C z * (D z * D z)) := by
    have hC0 : 0 ≤ C z := by dsimp only [C]; positivity
    have hD1 : 1 ≤ D z := by
      dsimp only [D]
      linarith [norm_nonneg (fderiv ℝ G z), norm_nonneg (fderiv ℝ (fderiv ℝ G) z)]
    have houter (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i f (G z)‖ ≤ C z := by
      have hi2 : i ≤ 2 := hi.trans hj
      interval_cases i
      · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        dsimp only [C]
        linarith [norm_nonneg (fderiv ℝ f (G z)), norm_nonneg (fderiv ℝ (fderiv ℝ f) (G z))]
      · rw [norm_iteratedFDeriv_one]
        dsimp only [C]
        linarith [abs_nonneg (f (G z)), norm_nonneg (fderiv ℝ (fderiv ℝ f) (G z))]
      · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
        dsimp only [C]
        linarith [abs_nonneg (f (G z)), norm_nonneg (fderiv ℝ f (G z))]
    have hinner (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
        ‖iteratedFDeriv ℝ i G z‖ ≤ D z ^ i := by
      have hi2 : i ≤ 2 := hij.trans hj
      interval_cases i
      · rw [pow_one, norm_iteratedFDeriv_one]
        dsimp only [D]
        linarith [norm_nonneg (fderiv ℝ (fderiv ℝ G) z)]
      · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
        apply (show ‖fderiv ℝ (fderiv ℝ G) z‖ ≤ D z by
          dsimp only [D]
          linarith [norm_nonneg (fderiv ℝ G z)]).trans
        exact le_self_pow₀ hD1 (by norm_num)
    have H := norm_iteratedFDeriv_comp_le hf.1 hG (by exact_mod_cast hj) z
      (C := C z) (D := D z) houter hinner
    calc
      _ ≤ (j.factorial : ℝ) * C z * D z ^ j := H
      _ ≤ 2 * C z * D z ^ 2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hC0
        · exact pow_le_pow_right₀ hD1 hj
        · positivity
        · positivity
      _ = _ := by ring
  have hfull : ParamSmooth (fun z => f (G z)) := by
    refine ⟨hf.1.comp hG, hg0, ?_, ?_⟩
    · apply henv.of_norm_le (K := 2) (by norm_num)
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [C, D]; positivity)]
      simpa only [norm_iteratedFDeriv_one] using hjet 1 (by norm_num) z
    · apply henv.of_norm_le (K := 2) (by norm_num)
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [C, D]; positivity)]
      simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one,
        norm_iteratedFDeriv_zero] using hjet 2 le_rfl z
  simpa only [hGeq] using hfull

theorem regular_affineBilinear {f : P × X → ℝ} (hf : ParamRegular f)
    (A : Y →L[ℝ] X) (L : P →L[ℝ] Y →L[ℝ] X) :
    ParamRegular (fun z : P × Y => f (z.1, A z.2 + L z.1 z.2)) := by
  have hs := smooth_affineBilinear hf.toSmooth A L
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro R
  obtain ⟨C, hC, hbound⟩ := hf.2.1 R
  let D : ℝ := ‖A‖ + ‖L‖ * max R 0
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C * (1 + D), by positivity, ?_⟩
  intro p y hp
  apply (hbound p (A y + L p y) hp).trans
  have hb : ‖A y + L p y‖ ≤ D * ‖y‖ := affineBilinear_bound A L hp y
  nlinarith [mul_le_mul_of_nonneg_left hb hC, mul_nonneg hC hD,
    mul_nonneg hC (norm_nonneg y)]

end Composition

section ExponentialParameters

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem regular_parameterCLM (M : P →L[ℝ] ℝ) :
    ParamRegular (fun z : P × X => M z.1) := by
  let K : P × X →L[ℝ] ℝ := M.comp (ContinuousLinearMap.fst ℝ P X)
  have hd : fderiv ℝ (fun z : P × X => M z.1) = fun _ => K :=
    funext (fun z => K.fderiv)
  refine ⟨K.contDiff, ?_, ?_, ?_⟩
  · intro R
    refine ⟨‖M‖ * max R 0, by positivity, ?_⟩
    intro p x hp
    calc
      |M p| ≤ ‖M‖ * ‖p‖ := M.le_opNorm p
      _ ≤ ‖M‖ * max R 0 := mul_le_mul_of_nonneg_left
        (hp.trans (le_max_left _ _)) (norm_nonneg M)
      _ ≤ (‖M‖ * max R 0) * (1 + ‖x‖) :=
        le_mul_of_one_le_right (by positivity) (by linarith [norm_nonneg x])
  · rw [hd]
    exact ParamExpGrowth.of_bounded (norm_nonneg K) (fun _ => le_rfl)
  · rw [hd]
    have hzero : fderiv ℝ (fun _ : P × X => K) =
        fun _ => (0 : P × X →L[ℝ] P × X →L[ℝ] ℝ) :=
      funext (fun z => fderiv_const_apply K)
    rw [hzero]
    exact ParamExpGrowth.of_bounded
      (f := fun _ : P × X => (0 : P × X →L[ℝ] P × X →L[ℝ] ℝ)) (C := 0) le_rfl
      (fun _ => le_of_eq ContinuousLinearMap.opNorm_zero)

theorem regular_exp_parameter (M : P →L[ℝ] ℝ) :
    ParamRegular (fun z : P × X => Real.exp (M z.1)) := by
  have hs := (regular_parameterCLM (X := X) M).expSmooth
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro R
  refine ⟨Real.exp (‖M‖ * max R 0), (Real.exp_pos _).le, ?_⟩
  intro p x hp
  rw [abs_of_pos (Real.exp_pos _)]
  have hb : M p ≤ ‖M‖ * max R 0 :=
    (le_abs_self _).trans ((M.le_opNorm p).trans
      (mul_le_mul_of_nonneg_left (hp.trans (le_max_left _ _)) (norm_nonneg M)))
  exact (Real.exp_le_exp.mpr hb).trans
    (le_mul_of_one_le_right (Real.exp_pos _).le (by linarith [norm_nonneg x]))

theorem regular_mul_exp_parameter {F : P × X → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) : ParamRegular (fun z => Real.exp (M z.1) * F z) := by
  have hs := (regular_exp_parameter (X := X) M).toSmooth.mul hF.toSmooth
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro R
  obtain ⟨C, hC, hbound⟩ := hF.2.1 R
  refine ⟨Real.exp (‖M‖ * max R 0) * C, by positivity, ?_⟩
  intro p x hp
  have hb : M p ≤ ‖M‖ * max R 0 :=
    (le_abs_self _).trans ((M.le_opNorm p).trans
      (mul_le_mul_of_nonneg_left (hp.trans (le_max_left _ _)) (norm_nonneg M)))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul (Real.exp_le_exp.mpr hb) (hbound p x hp) (abs_nonneg _)
    (Real.exp_pos _).le).trans_eq (by ring)

private def translationBilinear (V : P →L[ℝ] X) : P →L[ℝ] (X × ℝ) →L[ℝ] X :=
  (((ContinuousLinearMap.compL ℝ (X × ℝ) ℝ X).flip
    (ContinuousLinearMap.snd ℝ X ℝ)).comp (ContinuousLinearMap.lsmul ℝ ℝ).flip).comp V

theorem regular_movingInput {F : P × X → ℝ} (hF : ParamRegular F) (V : P →L[ℝ] X) :
    ParamRegular (fun z : P × (X × ℝ) => F (z.1, z.2.1 + z.2.2 • V z.1)) := by
  exact regular_affineBilinear hF (ContinuousLinearMap.fst ℝ X ℝ) (translationBilinear V)

theorem smooth_movingInput {G : P × X → ℝ} (hG : ParamSmooth G) (V : P →L[ℝ] X) :
    ParamSmooth (fun z : P × (X × ℝ) => G (z.1, z.2.1 + z.2.2 • V z.1)) := by
  exact smooth_affineBilinear hG (ContinuousLinearMap.fst ℝ X ℝ) (translationBilinear V)

theorem regular_movingStep {F : P × X → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] X) :
    ParamRegular (fun z : P × X => vectorStep (Real.exp (M z.1)) (V z.1)
      (fun y => F (z.1,y)) z.2) := by
  let H : P × (X × ℝ) → ℝ := fun z =>
    Real.exp (M z.1) * F (z.1, z.2.1 + z.2.2 • V z.1)
  have hH : ParamRegular H := regular_mul_exp_parameter (regular_movingInput hF V) M
  have hZ := hH.gaussianStep 1
  have hQ := regular_mul_exp_parameter hZ (-M)
  convert hQ using 1
  funext z
  simp only [vectorStep, gaussianStep, Real.exp_ne_zero, ite_false, one_ne_zero,
    positiveGaussianLogStep, H, one_mul, neg_apply,
    Real.exp_neg, div_eq_mul_inv]
  ring

theorem smooth_movingAverage {F G : P × X → ℝ} (hF : ParamRegular F) (hG : ParamSmooth G)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] X) :
    ParamSmooth (fun z : P × X => vectorStepAverage (Real.exp (M z.1)) (V z.1)
      (fun y => F (z.1,y)) (fun y => G (z.1,y)) z.2) := by
  have hH := regular_mul_exp_parameter (regular_movingInput hF V) M
  have hT := smooth_movingInput hG V
  have hA := ParamSmooth.gaussianAverage hH hT 1
  convert hA using 1
  funext z
  simp only [vectorStepAverage, OAI.SK.Analytic.gaussianAverage, gaussianStepLaw, one_mul]

def exponentialSteps (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] X))) (p : P) : List (ℝ × X) :=
  ps.map (fun q => (Real.exp (q.1 p), q.2 p))

def exponentialChain (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] X)))
    (F : P × X → ℝ) (z : P × X) : ℝ :=
  vectorIncrementChain (exponentialSteps ps z.1) (fun y => F (z.1,y)) z.2

theorem regular_exponentialChain (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] X)))
    {F : P × X → ℝ} (hF : ParamRegular F) : ParamRegular (exponentialChain ps F) := by
  induction ps with
  | nil => exact hF
  | cons q ps ih =>
    exact regular_movingStep ih q.1 q.2

def exponentialAverage (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] X)))
    (F G : P × X → ℝ) (z : P × X) : ℝ :=
  vectorIncrementAverage (exponentialSteps ps z.1) (fun y => F (z.1,y))
    (fun y => G (z.1,y)) z.2

theorem smooth_exponentialAverage (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] X)))
    {F G : P × X → ℝ} (hF : ParamRegular F) (hG : ParamSmooth G) :
    ParamSmooth (exponentialAverage ps F G) := by
  induction ps with
  | nil => exact hG
  | cons q ps ih =>
    exact smooth_movingAverage (regular_exponentialChain ps hF) ih q.1 q.2

end ExponentialParameters

section LocalCurves

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

abbrev Coordinates (n : ℕ) (X : Type) := Fin n → ℝ × X

def coordinateSteps (n : ℕ) :
    List ((Coordinates n X →L[ℝ] ℝ) × (Coordinates n X →L[ℝ] X)) :=
  List.ofFn (fun i : Fin n =>
    ((ContinuousLinearMap.fst ℝ ℝ X).comp (ContinuousLinearMap.proj i),
     (ContinuousLinearMap.snd ℝ ℝ X).comp (ContinuousLinearMap.proj i)))

def logParameters (ps : List (ℝ → ℝ × X)) (k : ℝ) : Coordinates ps.length X :=
  fun i => (Real.log ((ps.get i k).1), (ps.get i k).2)

theorem coordinateSteps_apply (ps : List (ℝ → ℝ × X)) (k : ℝ)
    (hm : ∀ p ∈ ps, 0 < (p k).1) :
    exponentialSteps (coordinateSteps ps.length) (logParameters ps k) = ps.map (fun p => p k) := by
  rw [exponentialSteps, coordinateSteps, List.map_ofFn]
  have heq : (fun i : Fin ps.length =>
      (Real.exp (((ContinuousLinearMap.fst ℝ ℝ X).comp (ContinuousLinearMap.proj i))
        (logParameters ps k)),
       ((ContinuousLinearMap.snd ℝ ℝ X).comp (ContinuousLinearMap.proj i)) (logParameters ps k))) =
      fun i => ps.get i k := by
    funext i
    change (Real.exp (Real.log ((ps.get i k).1)), (ps.get i k).2) = ps.get i k
    rw [Real.exp_log (hm _ (List.get_mem ps i)), Prod.mk.eta]
  simp only [Function.comp_def]
  rw [heq]
  simpa only [List.ofFn_get, Function.comp_def] using
    (List.map_ofFn (f := ps.get) (g := fun p => p k)).symm

theorem logParameters_contDiffAt (ps : List (ℝ → ℝ × X)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hm : ∀ p ∈ ps, 0 < (p k).1) :
    ContDiffAt ℝ 2 (logParameters ps) k := by
  apply contDiffAt_pi.mpr
  intro i
  exact ((hreg _ (List.get_mem ps i)).fst.log (hm _ (List.get_mem ps i)).ne').prodMk
    (hreg _ (List.get_mem ps i)).snd

private theorem eventually_positive_masses (ps : List (ℝ → ℝ × X)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hm : ∀ p ∈ ps, 0 < (p k).1) :
    ∀ᶠ t in 𝓝 k, ∀ p ∈ ps, 0 < (p t).1 := by
  have hget : ∀ᶠ t in 𝓝 k, ∀ i : Fin ps.length, 0 < (ps.get i t).1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hreg _ (List.get_mem ps i)).fst.continuousAt.eventually
      (Ioi_mem_nhds (hm _ (List.get_mem ps i)))
  filter_upwards [hget] with t ht p hp
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  exact ht i

theorem actual_chain_contDiffAt (ps : List (ℝ → ℝ × X)) {f : X → ℝ}
    (hf : ParamRegular (fun z : Coordinates ps.length X × X => f z.2))
    {k : ℝ} (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hm : ∀ p ∈ ps, 0 < (p k).1)
    (x : X) :
    ContDiffAt ℝ 2 (fun z : ℝ × X =>
      vectorIncrementChain (ps.map (fun p => p z.1)) f z.2) (k,x) := by
  have hP := logParameters_contDiffAt ps hreg hm
  have hU := regular_exponentialChain (coordinateSteps ps.length) hf
  have hcomp : ContDiffAt ℝ 2 (fun z : ℝ × X =>
      exponentialChain (coordinateSteps ps.length) (fun w => f w.2) (logParameters ps z.1,z.2)) (k,x) :=
    hU.1.contDiffAt.comp (k,x) ((hP.comp (k,x) contDiff_fst.contDiffAt).prodMk contDiff_snd.contDiffAt)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (eventually_positive_masses ps hreg hm)] with z hz
  dsimp only [exponentialChain]
  rw [coordinateSteps_apply ps z.1 hz]

theorem actual_average_contDiffAt (ps : List (ℝ → ℝ × X)) {f g : X → ℝ}
    (hf : ParamRegular (fun z : Coordinates ps.length X × X => f z.2))
    (hg : ParamSmooth (fun z : Coordinates ps.length X × X => g z.2))
    {k : ℝ} (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hm : ∀ p ∈ ps, 0 < (p k).1)
    (x : X) :
    ContDiffAt ℝ 2 (fun z : ℝ × X =>
      vectorIncrementAverage (ps.map (fun p => p z.1)) f g z.2) (k,x) := by
  have hP := logParameters_contDiffAt ps hreg hm
  have hU := smooth_exponentialAverage (coordinateSteps ps.length) hf hg
  have hcomp : ContDiffAt ℝ 2 (fun z : ℝ × X =>
      exponentialAverage (coordinateSteps ps.length) (fun w => f w.2) (fun w => g w.2)
        (logParameters ps z.1,z.2)) (k,x) :=
    hU.1.contDiffAt.comp (k,x) ((hP.comp (k,x) contDiff_fst.contDiffAt).prodMk contDiff_snd.contDiffAt)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (eventually_positive_masses ps hreg hm)] with z hz
  dsimp only [exponentialAverage]
  rw [coordinateSteps_apply ps z.1 hz]

end LocalCurves

section SpatialDerivative

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fderiv_step_average {f : X → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v x w : X) :
    fderiv ℝ (vectorStep m v f) x w =
      vectorStepAverage m v f (fun y => fderiv ℝ f y w) x := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  have H := fderiv_gaussianStep_apply (hf.compCLM (vectorTranslation v)) m x w
  change fderiv ℝ (vectorStep m v f) x w = _ at H
  rw [H]
  change (∫ t, prefixGradient (f ∘ vectorTranslation v) w (x,t)
    ∂gaussianStepLaw m (f ∘ vectorTranslation v) x) = _
  apply integral_congr_ae
  filter_upwards [] with t
  rw [prefixGradient, (hd ((vectorTranslation v) (x,t))).hasFDerivAt.comp
    (x,t) (vectorTranslation v).hasFDerivAt |>.fderiv]
  simp only [ContinuousLinearMap.comp_apply, vectorTranslation, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply, zero_smul, add_zero]

theorem fderiv_chain_average (ps : List (ℝ × X)) {f : X → ℝ} (hf : BoundedDerivs f)
    (x w : X) : fderiv ℝ (vectorIncrementChain ps f) x w =
      vectorIncrementAverage ps f (fun y => fderiv ℝ f y w) x := by
  induction ps generalizing x with
  | nil => rfl
  | cons p ps ih =>
    change fderiv ℝ (vectorStep p.1 p.2 (vectorIncrementChain ps f)) x w = _
    rw [fderiv_step_average (vectorIncrementChain_regular ps hf)]
    have heq : (fun y => fderiv ℝ (vectorIncrementChain ps f) y w) =
        vectorIncrementAverage ps f (fun y => fderiv ℝ f y w) := funext ih
    rw [heq]
    rfl

end SpatialDerivative

section ThreeDimensional

local notation "V3" => (Fin 3 → ℝ)

theorem regular_fixedTerminal {r : ℕ} {B : ℝ} {f : V3 → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ParamRegular (fun z : P × V3 => f z.2) := by
  have H := StepCalculus.paramRegular_affineBilinear (P := P) hf hr
    (ContinuousLinearMap.id ℝ V3) (0 : P →L[ℝ] V3 →L[ℝ] V3)
  simpa only [ContinuousLinearMap.id_apply, zero_apply, add_zero] using H

theorem contDiffAt_curveChain (ps : List (ℝ → ℝ × V3)) {r : ℕ} {B : ℝ} {f : V3 → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hm : ∀ p ∈ ps, 0 < (p k).1) (x : V3) :
    ContDiffAt ℝ 2 (fun z : ℝ × V3 =>
      vectorIncrementChain (ps.map (fun p => p z.1)) f z.2) (k,x) := by
  exact actual_chain_contDiffAt ps (regular_fixedTerminal hf hr _) hreg hm x

theorem contDiffAt_curveChain_spatial (ps : List (ℝ → ℝ × V3)) {r : ℕ} {B : ℝ} {f : V3 → ℝ}
    (hf : QPotential r B f) (hr : 3 ≤ r) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hm : ∀ p ∈ ps, 0 < (p k).1) (x w : V3) :
    ContDiffAt ℝ 2 (fun z : ℝ × V3 =>
      fderiv ℝ (vectorIncrementChain (ps.map (fun p => p z.1)) f) z.2 w) (k,x) := by
  have hfw : QBddSmooth 2 (B * ‖w‖) (fun y => fderiv ℝ f y w) := (hf.of_le hr).directional w
  have H := actual_average_contDiffAt ps (g := fun y => fderiv ℝ f y w)
    (regular_fixedTerminal hf (by omega) _)
    (regular_fixedTerminal hfw.potential le_rfl (Coordinates ps.length V3)).toSmooth hreg hm x
  have heq : (fun z : ℝ × V3 =>
      fderiv ℝ (vectorIncrementChain (ps.map (fun p => p z.1)) f) z.2 w) =
      fun z => vectorIncrementAverage (ps.map (fun p => p z.1)) f
        (fun y => fderiv ℝ f y w) z.2 := by
    funext z
    exact fderiv_chain_average _ (hf.boundedDerivs (by omega)) z.2 w
  rw [heq]
  exact H

end ThreeDimensional

end SKBarriers2.ParamChain
