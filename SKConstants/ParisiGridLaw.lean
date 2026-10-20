module
public import SKConstants.ParisiGridDiffusion
public import SKConstants.ParisiFinitePartialLaw
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFPartitionRepresentation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

lemma scalarStepAverage_eq_varianceTilted_sq {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (m v : ℝ) :
    scalarStepAverage m v f g = varianceTilted m (v^2) f g := by
  funext x
  rw [varianceTilted_eq_tiltedMean hf hg]
  unfold tiltedMean
  have hem : Measurable (fun z : ℝ => Real.exp (m*f z)) := (measurable_const.mul hf).exp
  have hwm : Measurable (fun z : ℝ => g z*Real.exp (m*f z)) := hg.mul hem
  rw [semigroup_eq_standardGaussian_scaled hwm v x, semigroup_eq_standardGaussian_scaled hem v x]
  unfold scalarStepAverage gaussianAverage
  rw [gaussianStepLaw_integral_inv_smul]
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => mul_comm _ _)

def prefixGridChain (α : ℝ → ℝ) (h : ℝ≥0) (i : ℕ) (δ : ℝ≥0) :=
  uniformGridChain α h i 0 ++ [(α ((i:ℝ)*h),δ)]

lemma prefixGridChain_duration (α : ℝ → ℝ) (h : ℝ≥0) (i : ℕ) (δ : ℝ≥0) :
    chainDuration (prefixGridChain α h i δ) = (i:ℝ≥0)*h+δ := by
  simp only [prefixGridChain,chainDuration,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
  change chainDuration (uniformGridChain α h i 0)+δ = _
  rw [uniformGridChain_duration]

lemma prefixGridChain_models (α : ℝ → ℝ) (h : ℝ≥0) (hh : 0 < h)
    (i : ℕ) (δ : ℝ≥0) (hδ : δ ≤ h) :
    TimeChainModels (gridCDF α h) 0 (prefixGridChain α h i δ) := by
  apply TimeChainModels.append
  · simpa using uniformGridChain_models α h hh i 0
  · rw [uniformGridChain_duration]
    simp only [zero_add,NNReal.coe_mul,NNReal.coe_natCast]
    change (∀ z ∈ Ico ((i:ℝ)*h) ((i:ℝ)*h+δ), gridCDF α h z=α ((i:ℝ)*h)) ∧ True
    refine ⟨fun z hz => gridCDF_eq_cell α (by exact_mod_cast hh) i ⟨hz.1,?_⟩,trivial⟩
    push_cast
    have hhδ : (δ:ℝ) ≤ h := hδ
    linarith [hz.2]

lemma prefixGridChain_average (α : ℝ → ℝ) (h : ℝ≥0) (i : ℕ) (δ : ℝ≥0)
    (β : ℝ) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β (prefixGridChain α h i δ) f g =
      scalarHierarchyAverage i (fun j => α ((j:ℝ)*h)) (fun _ => β*Real.sqrt h)
        (scalarTimeStep β (α ((i:ℝ)*h)) δ f)
        (scalarStepAverage (α ((i:ℝ)*h)) (β*Real.sqrt δ) f g) := by
  let p : Fin (i+1) → ℝ × ℝ≥0 :=
    Fin.lastCases (α ((i:ℝ)*h),δ) (fun j => (α ((j:ℝ)*h),h))
  have hp : List.ofFn p = prefixGridChain α h i δ := by
    rw [List.ofFn_succ']
    simp [p,prefixGridChain,uniformGridChain,List.concat_eq_append]
  rw [←hp,scalarTimeChainAverage_ofFn,scalarHierarchyAverage]
  simp only [p,Fin.lastCases_last,Fin.lastCases_castSucc,Prod.fst,Prod.snd,scalarTimeStep]

theorem finiteFeedback_grid_expectation_eq_scalarCDFAverage
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 0 < β) (α : ℝ → ℝ) (hα : Monotone α)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1)
    (h : ℝ≥0) (hh : 0 < h) (N : ℕ) (hN : (N:ℝ≥0)*h=1)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    (∫ w, g ((finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0))
      (softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0))
      (gridCDFCoefficient α h) (Real.toNNReal (β^2)*h) N 0).solution W.driver
        (Real.toNNReal (β^2*r)) w) ∂W.law) =
      scalarCDFAverage β (gridCDF α h) 0 (Real.toNNReal r)
        (scalarCDFValue β (gridCDF α h) r (Real.toNNReal (1-r))) g 0 := by
  obtain ⟨i,hi,δ,hδ,he⟩ := exists_grid_cell hh hN hr
  let c := gridCDFCoefficient α h
  let H : ℝ≥0 := Real.toNNReal (β^2)*h
  let d : ℝ≥0 := Real.toNNReal (β^2)*δ
  let F := varianceLogHeat (c i) ((H:ℝ)-d) (backwardBoundary c H (softAbs 1) N (i+1))
  have hf := regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0)
  have hLip := softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0)
  have hF : RegularDatum F := regularDatum_varianceLogHeat (cascade_regular hf hLip c H _ _)
    (cascade_lipschitz hLip c H _ _) (c i).coe_nonneg _
  have hFL : LipschitzWith 1 F := varianceLogHeat_lipschitz (cascade_lipschitz hLip c H _ _) (c i).coe_nonneg _
  have ht : Real.toNNReal (β^2*r) = (i:ℝ≥0)*H+d := by
    ext
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hr.1)]
    simp only [H,d,NNReal.coe_mul,NNReal.coe_add,Real.coe_toNNReal _ (sq_nonneg β),NNReal.coe_natCast]
    rw [he]; ring
  have hdH : d ≤ H := mul_le_mul_of_nonneg_left hδ.le (Real.toNNReal (β^2)).coe_nonneg
  have hFeq : F = scalarCDFValue β (gridCDF α h) r (Real.toNNReal (1-r)) := by
    have hv := finiteValue_grid_eq_scalarCDFValue α hα ha β h hh N hN hr
    have hstart : β^2*r=(i:ℝ)*H+d := by
      have ht' := congrArg ((↑) : ℝ≥0 → ℝ) ht
      simpa only [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hr.1),NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast] using ht'
    rw [hstart,finiteValue_shift hf hLip c H hi.le 0 d.coe_nonneg] at hv
    have hiN : N-i = (N-(i+1))+1 := by omega
    simp only [Nat.zero_add,hiN] at hv
    rw [finiteValue_head (softAbs 1) c H (N-(i+1)) i (NNReal.coe_le_coe.mpr hdH)] at hv
    exact hv
  have hft : BoundedSmooth (varianceTilted (c i) d F g) :=
    (varianceTilted_family hF hFL hg (c i).coe_nonneg).regular d
  rw [ht,finite_transition_tilted_partial W hf hLip hg c H hi d hdH,
    finiteFeedback_expectation_eq_scalarHierarchyAverage W hf hLip hft c H N i hi.le]
  change scalarHierarchyAverage i (fun j => (c j:ℝ)) (fun _ => Real.sqrt H)
    (backwardBoundary c H (softAbs 1) N i) (varianceTilted (c i) d F g) 0 = _
  have hm : ∀ p ∈ prefixGridChain α h i δ, p.1 ∈ Icc (0:ℝ) 1 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact uniformGridChain_mass α ha h i 0 p hp
    · have hp' : p=(α ((i:ℝ)*h),δ) := List.mem_singleton.mp hp
      rw [hp']; exact ha _
  have hdur : chainDuration (prefixGridChain α h i δ) = Real.toNNReal r := by
    rw [prefixGridChain_duration]
    ext
    simp only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,Real.coe_toNNReal _ hr.1]
    exact he.symm
  have hB := hg.bound.choose_spec
  have hC := hg.deriv.bound.choose_spec
  have hgs (x : ℝ) : HasDerivAt g (deriv g x) x := (hg.smooth.differentiable (by simp) x).hasDerivAt
  have hremaining : Real.toNNReal (1-r) ≤ 1 := by
    apply Real.toNNReal_le_iff_le_coe.mpr
    simp only [NNReal.coe_one]
    linarith [hr.1]
  have hprefix : Real.toNNReal r ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr hr.2.le
  have havg := scalarCDFAverage_eq_chainAverage
    (scalarCDFValue_regular β (show ∀ z, gridCDF α h z ∈ Icc (0:ℝ) 1 from fun z => ha _)
      (gridCDF_mono hα (by exact_mod_cast hh)) r (Real.toNNReal (1-r)) hremaining)
    hgs hg.deriv.smooth.continuous
    (scalarCDFValue_lipschitz β (show ∀ z, gridCDF α h z ∈ Icc (0:ℝ) 1 from fun z => ha _)
      (gridCDF_mono hα (by exact_mod_cast hh)) r (Real.toNNReal (1-r)) hremaining) hB hC β
    (show ∀ z, gridCDF α h z ∈ Icc (0:ℝ) 1 from fun z => ha _)
    (gridCDF_mono hα (by exact_mod_cast hh)) (prefixGridChain α h i δ) hm 0 _
    hprefix hdur
    (prefixGridChain_models α h hh i δ hδ.le) 0
  rw [havg,prefixGridChain_average,←hFeq]
  have hsuffix : backwardBoundary c H (softAbs 1) N i = scalarTimeStep β (α ((i:ℝ)*h)) δ F := by
    rw [←backwardBoundary_step hf hLip c H hi]
    have hrem : 0 ≤ (H:ℝ)-d := sub_nonneg.mpr hdH
    have hBL : LipschitzWith 1 (backwardBoundary c H (softAbs 1) N (i+1)) := cascade_lipschitz hLip c H _ _
    rw [show (H:ℝ)=(d:ℝ)+((H:ℝ)-d) by ring,
      varianceLogHeat_add hBL (c i).coe_nonneg d.coe_nonneg hrem]
    change varianceLogHeat (c i) d F = _
    rw [scalarTimeStep_eq_logSemigroup hF.smooth.continuous.measurable]
    funext x
    rw [varianceLogHeat_eq_logSemigroup_toNNReal hF.smooth.continuous.measurable,Real.toNNReal_coe]
    congr 2
    change (Real.toNNReal (α ((i:ℝ)*h)):ℝ)=α ((i:ℝ)*h)
    exact Real.coe_toNNReal _ (ha _).1
  rw [hsuffix,scalarStepAverage_eq_varianceTilted_sq hF.smooth.continuous.measurable hg.smooth.continuous.measurable]
  have hvδ : (β*Real.sqrt (δ:ℝ))^2=(d:ℝ) := by simp [d,mul_pow,Real.sq_sqrt δ.coe_nonneg,sq_nonneg]
  rw [hvδ]
  congr 1
  · funext j; simp [c,gridCDFCoefficient,Real.coe_toNNReal _ (ha _).1]
  · funext j
    simp only [H,NNReal.coe_mul,Real.coe_toNNReal _ (sq_nonneg β)]
    rw [Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq hβ.le]
  · dsimp [c,gridCDFCoefficient]
    rw [max_eq_left (ha _).1]

end SKConstants.ParisiFullSupport
