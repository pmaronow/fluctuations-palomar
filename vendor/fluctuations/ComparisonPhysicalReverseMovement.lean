module

public import ComparisonPhysicalScoreLedger
public import ActualBoundedMomentInterpolation
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalIncrementMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem physical_movement_second_eq_profile_increment (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {i j : ℕ} (hij : i ≤ j) :
    (∫z,‖actualSpinPath n steps id j z-actualSpinPath n steps id i z‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)=
      physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  let G := forwardFiltration (FeatureIndex n → ℝ) (FeatureIndex n → ℝ) (Spin n) steps.length
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hX := actualSpinPath_rooted_martingale n steps ha q0
  have hR : ∀k,∀ᵐ z ∂mu,‖X k z‖ ≤ 1 :=
    fun k=>ae_of_all _ (fun z=>actualSpinPath_norm_le n steps ha id k z)
  have hcond := condExp_terminalMeanProjection hX hR (N:=j) (i:=i) (j:=i) (le_refl i) hij (c:=0)
  have hmean : (∫z,terminalMeanProjection X j i 0 z ∂mu)=
      (∫z,terminalMeanProjection X i i 0 z ∂mu) := by
    calc
      _ = ∫z,mu[terminalMeanProjection X j i 0 | G i] z ∂mu :=
        (integral_condExp (G.le i)).symm
      _ = _ := integral_congr_ae hcond
  have hinner : (∫z,inner ℝ (X i z) (X j z) ∂mu)=(∫z,‖X i z‖^2 ∂mu) := by
    simpa only [terminalMeanProjection,sub_zero,real_inner_self_eq_norm_sq] using hmean
  have hni : Integrable (fun z=>‖X i z‖^2) mu := by
    have h := physicalCutNormPower_integrable n steps ha
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id i 2
    simpa only [← rootedHierarchyPathLaw_eq_physical] using h
  have hnj : Integrable (fun z=>‖X j z‖^2) mu := by
    have h := physicalCutNormPower_integrable n steps ha
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id j 2
    simpa only [← rootedHierarchyPathLaw_eq_physical] using h
  have hijI : Integrable (fun z=>inner ℝ (X i z) (X j z)) mu := by
    have hi := (terminalMeanProjection_memLp hX hR j i 0 1).integrable le_rfl
    change Integrable (fun z=>inner ℝ (X i z) (X j z)-0) mu at hi
    simpa only [sub_zero] using hi
  have he (z) : ‖X j z-X i z‖^2=‖X j z‖^2+‖X i z‖^2-2*inner ℝ (X i z) (X j z) := by
    rw [norm_sub_sq_real,real_inner_comm]
    ring
  change (∫z,‖X j z-X i z‖^2 ∂mu)=_
  simp_rw [he]
  have hsub := integral_sub (hnj.add hni) (hijI.const_mul 2)
  have hadd := integral_add hnj hni
  simp only [Pi.add_apply,Pi.sub_apply] at hsub hadd
  rw [hsub,hadd,integral_const_mul,hinner]
  change _=physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i
  dsimp only [physicalPathSecondMoment,mu,X]
  ring

theorem physical_movement_fourth_le_raw_interpolation (n l : ℕ) (hl : 2 < l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {xs : ℝ} (hxs : 0 < xs)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps.length+1) :
    physicalSideMovementMoment n steps q0 i j ≤
      (physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i)^
        (((l:ℝ)-2)/((l:ℝ)-1))*
      ((2*physicalRawRatio n l steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q0 k))
        id measurable_id)^(2*l)*(xs+physicalCutMass 0 steps j)^l)^
        (1/((l:ℝ)-1)) := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  let Z := fun z=>‖X j z-X i z‖^2
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hx (k : ℕ) : Measurable (X k) := actualSpinPath_measurable n steps ha id measurable_id k
  have hm : Measurable Z := ((hx j).sub (hx i)).norm.pow_const 2
  have hZ0 (z) : 0 ≤ Z z := sq_nonneg _
  have hZ4 (z) : Z z ≤ 4 := by
    have hb : ‖X j z-X i z‖ ≤ 2 := (norm_sub_le _ _).trans (by
      have hj := actualSpinPath_norm_le n steps ha id j z
      have hi := actualSpinPath_norm_le n steps ha id i z
      linarith)
    dsimp only [Z]
    nlinarith [norm_nonneg (X j z-X i z)]
  have hp : (2:ℝ) < l := by exact_mod_cast hl
  have H := integral_square_interpolation_of_bounded mu Z hm hZ0
    (by norm_num : (0:ℝ) ≤ 4) hZ4 hp
  have hfirst : (∫z,Z z ∂mu)=physicalPathSecondMoment n steps q0 j-
      physicalPathSecondMoment n steps q0 i :=
    physical_movement_second_eq_profile_increment n steps ha q0 hij
  have hsquare (z) : (Z z)^2=‖X j z-X i z‖^4 := by dsimp only [Z]; ring
  have hpower (z) : (Z z)^(l:ℝ)=‖physicalCutIncrement n steps id i j z‖^(2*l) := by
    rw [Real.rpow_natCast]
    dsimp only [Z,physicalCutIncrement,X]
    rw [← pow_mul]
  have hraw := physicalRawRatio_increment_moment n l (by omega : 0 < l) steps ha hxs
    (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id hij hj
  rw [← rootedHierarchyPathLaw_eq_physical] at hraw
  simp only [hsquare,hpower,hfirst] at H
  change physicalSideMovementMoment n steps q0 i j ≤ _ at H
  have he : 0 ≤ 1/((l:ℝ)-1) := div_nonneg zero_le_one (by linarith)
  have hpow := Real.rpow_le_rpow (integral_nonneg
    (fun z=>pow_nonneg (norm_nonneg (physicalCutIncrement n steps id i j z)) _)) hraw he
  exact H.trans (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg
    (by rw [← hfirst]; exact integral_nonneg hZ0) _))

end OAI.SKFluctuations
