module

public import CavitySavedStarPair
public import ComparisonDirectConcentration

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy

 theorem momentNorm_nat_power_eq_abs_integral {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ} {l : ℕ} (hl : 0 < l)
    (hm : MemLp f (ENNReal.ofReal (l:ℝ)) mu) :
    (momentNorm mu f (l:ℝ))^l = ∫ z, |f z|^l ∂mu := by
  unfold momentNorm
  rw [MemLp.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_ne_zero_iff.mpr (Nat.cast_pos.mpr hl)) ENNReal.ofReal_ne_top hm]
  simp only [ENNReal.toReal_ofReal (Nat.cast_nonneg l),Real.norm_eq_abs,Real.rpow_natCast]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun z => pow_nonneg (abs_nonneg _) _) _)]
  exact Real.rpow_inv_natCast_pow (integral_nonneg fun z => pow_nonneg (abs_nonneg _) _) (Nat.ne_of_gt hl)

end OAI.SKFluctuations.Hierarchy
namespace OAI.SKFluctuations
open Hierarchy

 def physicalBufferCenteredNorm (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (k : Fin (steps.length+1) → ℝ) (p : ℝ) : ℝ :=
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let A := fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
    (spinSource n) steps 0 k z.1 z.2).1
  momentNorm mu (fun z => A z-∫ z', A z' ∂mu) p

 def physicalBufferedNormBudget (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (km kp : Fin (steps.length+1) → ℝ) (p eta : ℝ) : ℝ :=
  2*physicalBufferCenteredNorm n steps q0 km p +
    2*physicalBufferCenteredNorm n steps q0 kp p +eta

 def physicalBufferedMovementBudget (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (km kp : Fin (steps.length+1) → ℝ) (p eta : ℝ) : ℝ :=
  4*physicalBufferedNormBudget n steps q0 km kp p eta +
    8*physicalBufferCenteredNorm n steps q0 km p +4*eta

 theorem physical_star_from_actual_buffers (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (km kp : Fin (steps.length+1) → ℝ)
    (hkm : ∀ j, 0  ≤  km j) (hkp : ∀ j, 0  ≤  kp j)
    (hnormm : ∑ j, pathMassDifferences steps 0 j*km j = 1)
    (hnormp : ∑ j, pathMassDifferences steps 0 j*kp j = 1)
    (fork t : ℕ) (hfN : fork  ≤  steps.length+1) (htN : t  ≤  steps.length+1)
    (hfm : ∀ j, pathMassDifferences steps 0 j*km j  ≠  0 → j.val  ≤  fork)
    (htm : ∀ j, pathMassDifferences steps 0 j*km j  ≠  0 → j.val  ≤  t)
    (hfp : ∀ j, pathMassDifferences steps 0 j*kp j  ≠  0 → fork  ≤  j.val)
    (htp : ∀ j, pathMassDifferences steps 0 j*kp j  ≠  0 → t  ≤  j.val)
    {S eta tau : ℝ} (heta : 0  ≤  eta) (htau : 0 < tau)
    (hmeanm : |(∑ j, pathMassDifferences steps 0 j*km j *
      physicalPathSecondMoment n steps q0 j.val)-S|  ≤  eta)
    (hmeanp : |(∑ j, pathMassDifferences steps 0 j*kp j *
      physicalPathSecondMoment n steps q0 j.val)-S|  ≤  eta) :
    let mu0 := Measure.pi fun i => gaussianReal 0 (q0 i)
    let p := (2*l:ℕ)
    let Z := physicalBufferedNormBudget n steps q0 km kp p eta
    let M := physicalBufferedMovementBudget n steps q0 km kp p eta
    physicalStarPairMoment n l steps mu0 id measurable_id fork S  ≤ 
      (3:ℝ)^(2*l-1)*(physicalOverlapProjectionErrorMoment n l steps mu0 id measurable_id fork t +
        (2:ℝ)^(4*l-2)*(M^(2*l)/tau+tau*(|S|+Z)^(2*l)) + Z^(2*l)) := by
  dsimp only
  let mu0 := Measure.pi fun i => gaussianReal 0 (q0 i)
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  let p : ℝ := (2*l:ℕ)
  let Z := physicalBufferedNormBudget n steps q0 km kp p eta
  let M := physicalBufferedMovementBudget n steps q0 km kp p eta
  letI := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hp : 1  ≤  p := by dsimp [p]; exact_mod_cast (by omega : 1 ≤ 2*l)
  have hZ : 0  ≤  Z := by
    dsimp [Z,physicalBufferedNormBudget,physicalBufferCenteredNorm]
    have hm := momentNorm_nonneg (μ := mu) (fun z =>
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 km z.1 z.2).1 -
        ∫ w, (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 km w.1 w.2).1 ∂mu) p
    have hp' := momentNorm_nonneg (μ := mu) (fun z =>
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 kp z.1 z.2).1 -
        ∫ w, (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 kp w.1 w.2).1 ∂mu) p
    change 0 ≤ 2*_+2*_+eta
    positivity
  have hM : 0  ≤  M := by
    dsimp [M,physicalBufferedMovementBudget]
    have hCm := momentNorm_nonneg (μ := mu) (fun z =>
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 km z.1 z.2).1 -
        ∫ w, (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 km w.1 w.2).1 ∂mu) p
    change 0 ≤ 4*Z+8*_+4*eta
    positivity
  have hcenter (i : ℕ) (hiN : i ≤ steps.length+1)
      (him : ∀ j, pathMassDifferences steps 0 j*km j ≠ 0 → j.val ≤ i)
      (hip : ∀ j, pathMassDifferences steps 0 j*kp j ≠ 0 → i ≤ j.val) :
      momentNorm mu (fun z => ‖X i z‖^2-S) p  ≤  Z :=
    physical_buffered_norm_concentration n steps ha q0 km kp hkm hkp hnormm hnormp hiN
      him hip hp heta hmeanm hmeanp
  have hnf := hcenter fork hfN hfm hfp
  have hnt := hcenter t htN htm htp
  have hmove : momentNorm mu (fun z => ‖X t z-X fork z‖^2) p  ≤  M := by
    have H := physical_central_movement_moment n steps ha q0 km hkm hnormm htN hfN
      htm hfm hp heta hmeanm
    change momentNorm mu (fun z => ‖X t z-X fork z‖^2) p  ≤  _ at H
    dsimp only [M,physicalBufferedMovementBudget]
    dsimp only [physicalBufferCenteredNorm] at ⊢
    linarith
  have hsqmem (i : ℕ) : MemLp (fun z => ‖X i z‖^2) (ENNReal.ofReal p) mu := by
    apply MemLp.of_bound ((actualSpinPath_measurable n steps ha id measurable_id i).norm.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have H := actualSpinPath_norm_le n steps ha id i z
    nlinarith [norm_nonneg (X i z)]
  have hcmem (i : ℕ) : MemLp (fun z => ‖X i z‖^2-S) (ENNReal.ofReal p) mu :=
    (hsqmem i).sub (memLp_const S)
  have hanchor (i : ℕ) (hc : momentNorm mu (fun z => ‖X i z‖^2-S) p  ≤  Z) :
      (∫ z, ‖X i z‖^(4*l) ∂mu)  ≤  (|S|+Z)^(2*l) := by
    have H := momentNorm_add_le hp (hcmem i) (memLp_const S)
    simp only [sub_add_cancel,momentNorm_const S (by linarith : 0<p)] at H
    have hi : momentNorm mu (fun z => ‖X i z‖^2) p  ≤  |S|+Z := by linarith
    have Hpow := pow_le_pow_left₀ (momentNorm_nonneg _ _) hi (2*l)
    rw [momentNorm_nat_power_eq_abs_integral (by omega : 0<2*l) (hsqmem i)] at Hpow
    simpa only [abs_sq,←pow_mul,show 2*(2*l)=4*l by omega] using Hpow
  have hmovemem : MemLp (fun z => ‖X t z-X fork z‖^2) (ENNReal.ofReal p) mu := by
    apply MemLp.of_bound (((actualSpinPath_measurable n steps ha id measurable_id t).sub
      (actualSpinPath_measurable n steps ha id measurable_id fork)).norm.pow_const 2).aestronglyMeasurable 4
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have H := norm_sub_le (X t z) (X fork z)
    have ht := actualSpinPath_norm_le n steps ha id t z
    have hf := actualSpinPath_norm_le n steps ha id fork z
    change ‖X t z-X fork z‖^2 ≤ 4
    change ‖X t z‖ ≤ 1 at ht
    change ‖X fork z‖ ≤ 1 at hf
    nlinarith [norm_nonneg (X t z-X fork z)]
  have hmovepow : (∫ z, ‖X t z-X fork z‖^(4*l) ∂mu)  ≤  M^(2*l) := by
    have H := pow_le_pow_left₀ (momentNorm_nonneg _ _) hmove (2*l)
    rw [momentNorm_nat_power_eq_abs_integral (by omega : 0<2*l) hmovemem] at H
    simpa only [abs_sq,←pow_mul,show 2*(2*l)=4*l by omega] using H
  have hnormpow : (∫ z, |‖X fork z‖^2-S|^(2*l) ∂mu)  ≤  Z^(2*l) := by
    have H := pow_le_pow_left₀ (momentNorm_nonneg _ _) hnf (2*l)
    rwa [momentNorm_nat_power_eq_abs_integral (by omega : 0<2*l) (hcmem fork)] at H
  have hcentral := physicalCentralPairError_moment_le n l hl steps ha mu0 id measurable_id fork t htau
  rw [← rootedHierarchyPathLaw_eq_physical] at hcentral
  have hcentral' : (∫ z, conditionalForkTest (uniformWeight n) (finiteFeature n) steps id fork
      (fun zz => |physicalCentralPairError n steps id fork t zz|^(2*l)) z ∂mu)  ≤ 
      (2:ℝ)^(4*l-2)*(M^(2*l)/tau+tau*(|S|+Z)^(2*l)) := by
    apply hcentral.trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
    have ha := add_le_add (hanchor t hnt) (hanchor fork hnf)
    have hm := div_le_div_of_nonneg_right hmovepow htau.le
    have hn := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ tau/2)
    change _  ≤  _ at hm hn
    nlinarith
  have H := physicalStarPairMoment_le_finite_ledger n l hl steps ha mu0 id measurable_id fork t S
  rw [← rootedHierarchyPathLaw_eq_physical] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  exact add_le_add (add_le_add le_rfl hcentral') hnormpow

end OAI.SKFluctuations
