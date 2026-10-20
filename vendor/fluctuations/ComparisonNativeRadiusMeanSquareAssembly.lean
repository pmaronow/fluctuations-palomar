module

public import ComparisonNativeRadiusSideDominance
public import ComparisonNativeRadiusDefectRawCovariance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3500000
attribute [local instance] Classical.propDecidable

theorem radius_physical_ordered_integrated_defect_le_raw_covariance (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (mass : Fin (steps.length+1)→ℝ)
    (G : Finset (Fin (steps.length+1)))
    (hmass : ∀j,0 ≤ mass j)
    (hzero : ∀j,pathMassDifferences steps 0 j=0→mass j=0)
    {xs y delta eta V : ℝ} (hxs : 0 < xs) (hy : 0 ≤ y) (hd : 0 < delta)
    (heta : 0 ≤ eta) (hV : 0 ≤ V)
    (hl : ∀i∈G,delta ≤ NativeRadiusSide.before mass i)
    (hr : ∀i∈G,delta ≤ NativeRadiusSide.after mass i)
    (hband : ∀i,mass i≠0→xs+physicalCutMass 0 steps i.val ≤ y)
    (hS : ∀i,mass i≠0→∀j,mass j≠0→
      |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i.val| ≤ eta)
    (hvarianceL : ∀i∈G,selectedScoreVariance n steps q0
      (NativeRadiusSide.leftCoefficient (pathMassDifferences steps 0) mass i) ≤ V)
    (hvarianceR : ∀i∈G,selectedScoreVariance n steps q0
      (NativeRadiusSide.rightCoefficient (pathMassDifferences steps 0) mass i) ≤ V)
    :
    let Q := physicalRawRatio n 2 steps 0 xs
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
    let v := ∑i,mass i
    let T := ∑i,mass i*actualCutCovarianceEnergy n steps q0 i.val
    (∑i,mass i*actualCutReplicaDefect n steps q0 i.val
      (physicalPathSecondMoment n steps q0 i.val)) ≤
      (48*V+6*eta^2)*v+
        256*Q^2*y*Real.sqrt ((1+v/delta)*T)*Real.sqrt v+T+
        Q^4*y^2*(∑i,if i∈G then 0 else mass i)+
        2*Q^2*y*Real.sqrt T*Real.sqrt (∑i,if i∈G then 0 else mass i) := by
  dsimp only
  let Q := physicalRawRatio n 2 steps 0 xs
    (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
  let C := fun i:Fin (steps.length+1)=>actualCutCovarianceEnergy n steps q0 i.val
  let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
    (physicalPathSecondMoment n steps q0 i.val)
  let noise := fun i j:Fin (steps.length+1)=>physicalSideNoiseMoment n steps q0 i.val j.val
  let PL := NativeRadiusSide.leftJoint mass G
  let PR := NativeRadiusSide.rightJoint mass G
  let v := ∑i,mass i
  let T := ∑i,mass i*C i
  let edge := fun i:Fin (steps.length+1)=>if i∈G then 0 else mass i
  let cost := 48*V+6*eta^2
  let A := 4*Q^2*y
  have hv : 0 ≤ v := Finset.sum_nonneg (fun i _=>hmass i)
  have hC i : 0 ≤ C i := actualCutCovarianceEnergy_nonneg n steps ha q0 i.val
  have hcost : 0 ≤ cost := by dsimp only [cost];positivity
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hLP i (hi : i∈G) : 0 < NativeRadiusSide.before mass i := by
    exact hd.trans_le (hl i hi)
  have hRP i (hi : i∈G) : 0 < NativeRadiusSide.after mass i := by
    exact hd.trans_le (hr i hi)
  have hPnL i j : 0 ≤ PL i j := NativeRadiusSide.leftJoint_nonneg mass G hmass i j
  have hPnR i j : 0 ≤ PR i j := NativeRadiusSide.rightJoint_nonneg mass G hmass i j
  have hNoiseL i j (hp : PL i j≠0) : noise i j ≤ A*Real.sqrt (C i+C j) := by
    have hmi : mass i≠0 := by
      intro hi
      exact hp (by simp [PL,NativeRadiusSide.leftJoint,hi])
    have hmj : mass j≠0 := by
      intro hj
      exact hp (by simp [PL,NativeRadiusSide.leftJoint,NativeRadiusSide.leftProbability,hj])
    exact radius_physicalSideNoiseMoment_le_raw_covariance n steps ha q0 hxs
      (by omega) (by omega) (hband i hmi) (hband j hmj)
  have hNoiseR i j (hp : PR i j≠0) : noise i j ≤ A*Real.sqrt (C i+C j) := by
    have hmi : mass i≠0 := by
      intro hi
      exact hp (by simp [PR,NativeRadiusSide.rightJoint,hi])
    have hmj : mass j≠0 := by
      intro hj
      exact hp (by simp [PR,NativeRadiusSide.rightJoint,NativeRadiusSide.rightProbability,hj])
    exact radius_physicalSideNoiseMoment_le_raw_covariance n steps ha q0 hxs
      (by omega) (by omega) (hband i hmi) (hband j hmj)
  have hNL := NativeRadiusSide.joint_raw_noise_le PL mass C noise hPnL hmass hC
    (div_nonneg hv hd.le) hA
    (NativeRadiusSide.leftJoint_row_le mass G hmass (fun i hi=>hLP i hi))
    (NativeRadiusSide.leftJoint_column_le mass G hmass hd hl) hNoiseL
  have hNR := NativeRadiusSide.joint_raw_noise_le PR mass C noise hPnR hmass hC
    (div_nonneg hv hd.le) hA
    (NativeRadiusSide.rightJoint_row_le mass G hmass (fun i hi=>hRP i hi))
    (NativeRadiusSide.rightJoint_column_le mass G hmass hd hr) hNoiseR
  have hedge i : 0 ≤ edge i := by dsimp only [edge];split_ifs; exact le_rfl; exact hmass i
  have hedgeLe i : edge i ≤ mass i := by dsimp only [edge];split_ifs <;> simp [hmass i]
  have hcross := weighted_sqrt_product_le edge C (fun _=>1) hedge hC (fun _=>by norm_num)
  simp only [Real.sqrt_one,mul_one] at hcross
  have hedgeEnergy : (∑i,edge i*C i) ≤ T :=
    Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hedgeLe i) (hC i))
  have hcrossBound : (∑i,edge i*Real.sqrt (C i)) ≤ Real.sqrt T*Real.sqrt (∑i,edge i) :=
    hcross.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hedgeEnergy) (Real.sqrt_nonneg _))
  have hpoint i : mass i*D i ≤ cost*mass i+
      32*(∑j,PL i j*noise i j)+32*(∑j,PR i j*noise i j)+mass i*C i+
      Q^4*y^2*edge i+2*Q^2*y*(edge i*Real.sqrt (C i)) := by
    by_cases hm : mass i=0
    · have hpl j : PL i j=0 := by simp [PL,NativeRadiusSide.leftJoint,hm]
      have hpr j : PR i j=0 := by simp [PR,NativeRadiusSide.rightJoint,hm]
      simp only [hm,mul_zero,zero_mul,hpl,hpr,Finset.sum_const_zero,add_zero]
      simp [edge,hm]
    by_cases hi : i∈G
    · have h := radius_physical_ordered_score_ledger n steps ha q0 mass hmass hzero i hm
        (hLP i hi) (hRP i hi) heta (hS i hm)
      dsimp only at h
      have hV1 := hvarianceL i hi
      have hV2 := hvarianceR i hi
      have hmle := mul_le_mul_of_nonneg_left h (hmass i)
      have hV1m := mul_le_mul_of_nonneg_left hV1 (mul_nonneg (hmass i) (by norm_num : (0:ℝ)≤24))
      have hV2m := mul_le_mul_of_nonneg_left hV2 (mul_nonneg (hmass i) (by norm_num : (0:ℝ)≤24))
      have hpL : (∑j,PL i j*noise i j)=mass i*(∑j,NativeRadiusSide.leftProbability mass i j*noise i j) := by
        simp only [PL,NativeRadiusSide.leftJoint,hi,ite_eq_left,mul_assoc,←Finset.mul_sum]
      have hpR : (∑j,PR i j*noise i j)=mass i*(∑j,NativeRadiusSide.rightProbability mass i j*noise i j) := by
        simp only [PR,NativeRadiusSide.rightJoint,hi,ite_eq_left,mul_assoc,←Finset.mul_sum]
      rw [hpL,hpR]
      simp only [edge,hi,ite_true,zero_mul,mul_zero,add_zero]
      dsimp only [cost,D,C,noise] at *
      nlinarith
    · have h := radius_actualCenteredCutReplicaDefect_le_raw_covariance n steps ha q0 hxs
        (i:=i.val) (by omega) (hband i hm)
      have hpl j : PL i j=0 := by simp [PL,NativeRadiusSide.leftJoint,hi]
      have hpr j : PR i j=0 := by simp [PR,NativeRadiusSide.rightJoint,hi]
      simp only [hpl,hpr,zero_mul,Finset.sum_const_zero,mul_zero,add_zero,edge,hi,ite_false]
      have hh := mul_le_mul_of_nonneg_left h (hmass i)
      have hc := mul_nonneg hcost (hmass i)
      dsimp only [Q,D,C] at hh ⊢
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have hnL := mul_le_mul_of_nonneg_left hNL (by norm_num : 0 ≤ (32:ℝ))
  have hnR := mul_le_mul_of_nonneg_left hNR (by norm_num : 0 ≤ (32:ℝ))
  have hnE := mul_le_mul_of_nonneg_left hcrossBound (by positivity : 0 ≤ 2*Q^2*y)
  change (∑i,mass i*D i) ≤ _
  dsimp only [v,T,cost,A,Q,edge] at hs hnL hnR hnE ⊢
  nlinarith

namespace LaplaceWindowFormalization
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonNativeRadiusRowMass_support_upper {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    {a z : ℝ} (hz : z∈Icc (0:ℝ) 1)
    (i : Fin ((sampleClockSteps q 0 as).length+1))
    (hi : comparisonNativeRadiusRowMass hc hk hkc hm hM q α as J a z i≠0) :
    physicalCutMass 0 (sampleClockSteps q 0 as) i.val < α.val.val z := by
  by_contra hn
  have hr := comparisonSweepQuantile_monotone hc hk hkc hm hM α (le_of_not_gt hn)
  rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α hz] at hr
  have he : Ioo a z ∩ Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps q 0 as) i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps q 0 as) (i.val+1)))=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro r h
    exact not_lt_of_ge (hr.trans h.2.1.le) h.1.2
  apply hi
  unfold comparisonNativeRadiusRowMass
  rw [he]
  split_ifs <;> simp

theorem comparisonNativeRadiusHeightBins_weighted_partition {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (S D : Fin ((sampleClockSteps q 0 as).length+1)→ℝ) {bins : ℕ} (hbins : 0<bins)
    (w a z : ℝ) :
    (∑b : Fin bins,∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM q α as
      (NativeRadiusHeight.bin S Finset.univ w b) a z i*D i)=
      ∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM q α as Finset.univ a z i*D i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_mul]
  congr 1
  simp only [comparisonNativeRadiusRowMass,NativeRadiusHeight.bin,Finset.mem_filter,
    Finset.mem_univ,true_and]
  let b0 : Fin bins := ⟨heightBin bins w (S i),heightBin_lt hbins _ _⟩
  have hb (b : Fin bins) : heightBin bins w (S i)=b.val ↔ b=b0 := by
    constructor
    · intro he;exact Fin.ext he.symm
    · intro he;subst b;rfl
  simp_rw [hb]
  simp

theorem comparison_native_radius_height_bin_defect_le (n : ℕ)
    (q : ℝ→FeatureIndex n→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh a z xs y delta w kmin V : ℝ}
    (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) (hxs : 0<xs)
    (hy : xs+α.val.val z ≤ y) (hd : 0<delta) (hw : 0<w)
    (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ k r)
    {bins : ℕ} (hbins : 0<bins) (hV : 0 ≤ V)
    (hheight : (physicalRawRatio n 2 (sampleClockSteps q 0 as) 0 xs
      (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id)^2*y ≤ (bins:ℝ)*w)
    (hvariance : comparisonDominatedRadiusVarianceBound n q as
      (comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α)
        α.val.val (Ioo a z) delta kmin) V) :
    let steps := sampleClockSteps q 0 as
    let Q := physicalRawRatio n 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id
    let mass := comparisonNativeRadiusRowMass hc hk hkc hm hM q α as Finset.univ a z
    let T := ∑i,mass i*actualCutCovarianceEnergy n steps (q 0) i.val
    let L := z-a
    let E := 2*delta+2*(mesh/c)
    (∑i,mass i*actualCutReplicaDefect n steps (q 0) i.val
      (physicalPathSecondMoment n steps (q 0) i.val)) ≤
      (48*V+6*w^2)*L+
        (bins:ℝ)*(256*Q^2*y*Real.sqrt ((1+L/delta)*T)*Real.sqrt L+T+
          Q^4*y^2*E+2*Q^2*y*Real.sqrt T*Real.sqrt E) := by
  dsimp only
  let steps := sampleClockSteps q 0 as
  let Q := physicalRawRatio n 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id
  let S := fun i:Fin (steps.length+1)=>physicalPathSecondMoment n steps (q 0) i.val
  let C := fun i:Fin (steps.length+1)=>actualCutCovarianceEnergy n steps (q 0) i.val
  let D := fun i:Fin (steps.length+1)=>actualCutReplicaDefect n steps (q 0) i.val (S i)
  let full := comparisonNativeRadiusRowMass hc hk hkc hm hM q α as Finset.univ a z
  let mass := fun b:Fin bins=>comparisonNativeRadiusRowMass hc hk hkc hm hM q α as
    (NativeRadiusHeight.bin S Finset.univ w b) a z
  let T := ∑i,full i*C i
  let L := z-a
  let E := 2*delta+2*(mesh/c)
  let cost := 48*V+6*w^2
  let rest := 256*Q^2*y*Real.sqrt ((1+L/delta)*T)*Real.sqrt L+T+
    Q^4*y^2*E+2*Q^2*y*Real.sqrt T*Real.sqrt E
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered q as ho
  have hf i : 0 ≤ full i := comparisonNativeRadiusRowMass_nonneg hc hk hkc hm hM q α as Finset.univ a z i
  have hm0 b i : 0 ≤ mass b i := comparisonNativeRadiusRowMass_nonneg hc hk hkc hm hM q α as _ a z i
  have hdom b i : mass b i ≤ full i := comparisonNativeRadiusRowMass_le_full hc hk hkc hm hM q α as _ a z i
  have hC i : 0 ≤ C i := actualCutCovarianceEnergy_nonneg n steps hs (q 0) i.val
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _=>mul_nonneg (hf i) (hC i))
  have hL : 0 ≤ L := sub_nonneg.mpr haz
  have hE : 0 ≤ E := by dsimp only [E];positivity
  have htotal : (∑i,full i)=L := comparisonNativeRadiusRowMass_total hc hk hkc hm hM q α as ho ha haz hz
  have hy0 : 0 ≤ y := by
    have halpha : 0 ≤ α.val.val z := by simpa only [α.property.1] using α.val.property.2 (ha.trans haz)
    linarith
  have hband b i (hi : mass b i≠0) : xs+physicalCutMass 0 steps i.val ≤ y := by
    have hu := comparisonNativeRadiusRowMass_support_upper hc hk hkc hm hM q α as _
      (show z∈Icc (0:ℝ) 1 from ⟨ha.trans haz,hz⟩) i hi
    exact (add_le_add_right hu.le xs).trans hy
  have hSm b i (hi : mass b i≠0) : S i∈Icc (0:ℝ) ((bins:ℝ)*w) := by
    have hraw := physicalProfile_second_le_raw_ratio n 2 (by norm_num) steps hs (q 0) hxs (i:=i.val)
      (by have h := i.isLt; change i.val<steps.length+1 at h; omega)
    have hmean0 : 0 ≤ S i := physicalPathSecondMoment_nonneg n steps (q 0) i.val
    exact ⟨hmean0,(hraw.trans (mul_le_mul_of_nonneg_left (hband b i hi) (sq_nonneg Q))).trans hheight⟩
  have hbinMem b i (hi : mass b i≠0) : i∈NativeRadiusHeight.bin S Finset.univ w b := by
    by_contra hn
    apply hi
    simp only [mass,comparisonNativeRadiusRowMass,hn,ite_false]
  have hdiam b i (hi : mass b i≠0) j (hj : mass b j≠0) : |S j-S i| ≤ w :=
    sameHeightBin_abs_le hbins hw (hSm b j hj) (hSm b i hi)
      ((Finset.mem_filter.mp (hbinMem b j hj)).2.trans (Finset.mem_filter.mp (hbinMem b i hi)).2.symm)
  have hv b : (∑i,mass b i) ≤ L := (Finset.sum_le_sum (fun i _=>hdom b i)).trans_eq htotal
  have hv0 b : 0 ≤ ∑i,mass b i := Finset.sum_nonneg (fun i _=>hm0 b i)
  have ht b : (∑i,mass b i*C i) ≤ T := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hdom b i) (hC i))
  have ht0 b : 0 ≤ ∑i,mass b i*C i := Finset.sum_nonneg (fun i _=>mul_nonneg (hm0 b i) (hC i))
  have hp b : (∑i,mass b i*D i) ≤ cost*(∑i,mass b i)+rest := by
    let G := NativeRadiusHeight.retainedRows (mass b) delta
    have hl i (hi : i∈G) : delta ≤ NativeRadiusSide.before (mass b) i :=
      (NativeRadiusHeight.retained_side_lengths _ _ hi).1
    have hr i (hi : i∈G) : delta ≤ NativeRadiusSide.after (mass b) i :=
      (NativeRadiusHeight.retained_side_lengths _ _ hi).2
    have hcoeff i (hi : i∈G) := comparisonNativeRadiusSideCoefficients_le_full hc hk hkc hm hM
      q α as ho he (NativeRadiusHeight.bin S Finset.univ w b) ha haz hz hd hkmin hfloor i (hl i hi) (hr i hi)
    have hVL i (hi : i∈G) : selectedScoreVariance n steps (q 0)
        (NativeRadiusSide.leftCoefficient (pathMassDifferences steps 0) (mass b) i) ≤ V := by
      simpa only [selectedScoreVariance] using hvariance _ (hcoeff i hi).1
    have hVR i (hi : i∈G) : selectedScoreVariance n steps (q 0)
        (NativeRadiusSide.rightCoefficient (pathMassDifferences steps 0) (mass b) i) ≤ V := by
      simpa only [selectedScoreVariance] using hvariance _ (hcoeff i hi).2
    have hh := radius_physical_ordered_integrated_defect_le_raw_covariance n steps hs (q 0) (mass b) G
      (hm0 b) (fun i h=>comparisonNativeRadiusRowMass_zero_of_zero_mass hc hk hkc hm hM q α as _ a z i h)
      hxs hy0 hd hw.le hV hl hr (hband b) (hdiam b) hVL hVR
    dsimp only at hh
    have heB : (∑i,if i∈G then 0 else mass b i) ≤ E := by
      simpa only [G,E,ite_not] using (comparisonNativeRadiusRows_strip_budget hc hk hkc hm hM q α as ho
        hmesh hmesh0 hd.le haz (NativeRadiusHeight.bin S Finset.univ w b)).1
    have hmul : (1+(∑i,mass b i)/delta)*(∑i,mass b i*C i) ≤ (1+L/delta)*T :=
      mul_le_mul (add_le_add_right (div_le_div_of_nonneg_right (hv b) hd.le) 1) (ht b)
        (ht0 b) (by positivity)
    have hn := mul_le_mul (Real.sqrt_le_sqrt hmul) (Real.sqrt_le_sqrt (hv b))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hecross := mul_le_mul (Real.sqrt_le_sqrt (ht b)) (Real.sqrt_le_sqrt heB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hn' := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 256*Q^2*y)
    have he' := mul_le_mul_of_nonneg_left heB (by positivity : 0 ≤ Q^4*y^2)
    have hecross' := mul_le_mul_of_nonneg_left hecross (by positivity : 0 ≤ 2*Q^2*y)
    dsimp only [rest,cost,Q,D,C,S] at *
    nlinarith [ht b]
  have hsum := Finset.sum_le_sum (fun b (_ : b∈Finset.univ)=>hp b)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hpart := comparisonNativeRadiusHeightBins_mass_partition hc hk hkc hm hM q α as
    Finset.univ S hbins w a z
  have hweighted := comparisonNativeRadiusHeightBins_weighted_partition hc hk hkc hm hM q α as S D hbins w a z
  change (∑b,∑i,mass b i)=∑i,full i at hpart
  change (∑b,∑i,mass b i*D i)=∑i,full i*D i at hweighted
  rw [hweighted,hpart,htotal] at hsum
  exact hsum

end
end LaplaceWindowFormalization

end OAI.SKFluctuations
