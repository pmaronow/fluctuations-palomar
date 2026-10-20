module

public import ComparisonActualHighWallRadiusUniformVariance
public import ComparisonShiftedNativeRadiusMeanSquareAssembly
public import ComparisonNativeRadiusQuantitative

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta0 cl cu Az C0 Ct D Bclock : ℝ}

theorem original_wall_radius_centered_defect_le
    (aM : ActualHighWallOverlapMinimum (n+1) margin delta0 cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ aM.data.N) (hlog : 1 ≤ Real.log aM.data.N) (hnd : 1/aM.data.N ≤ aM.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z xs y delta kmin B w : ℝ} (ha : aM.data.rmin < a) (haz : a ≤ z) (hz : z ≤ 1) (hxs : 0 < xs)
    (hy : xs+aM.alpha.val.val z ≤ y) (hdelta : 0 < delta) (hkmin : 0 < kmin)
    (hfloor : ∀r∈Ioo a z,kmin ≤ aM.data.k r)
    {bins : ℕ} (hbins : 0 < bins) (_hB : 0 ≤ B) (hw : 0 < w) (hwidth : B*y ≤ (bins:ℝ)*w)
    (hraw : ∀ᶠj in atTop,(physicalRawRatio (n+1) 2
      (sampleClockSteps (completedPathClock (n+1) aM.bf aM.hf) 0 (as j)) 0 xs
      (Measure.pi fun k=>gaussianReal 0 (completedPathClock (n+1) aM.bf aM.hf 0 k)) id measurable_id)^2 ≤ B) :
    let S:=aM.radiusS
    let F:=(n+1:ℝ)*(((1/3)/Real.log aM.data.N)*aM.data.g z)
    let V:=4*(S z-S a)/(aM.alpha.val.val a*delta^2*kmin*F)
    let T:=8*(S z-S a)/(aM.alpha.val.val a^2*F)
    (∫r in Ioo a z,aM.radiusB r-(S r)^2) ≤
      comparisonRadiusMeanSquareBudget bins (z-a) delta y B w V T (2*delta) := by
  dsimp only
  let m:=aM.shiftedNativeModel
  let bf:=aM.bf
  let hf:=aM.hf
  let q:=m.q
  let S := fun r=>aM.radiusS r
  let F := (n+1:ℝ)*(((1/3)/Real.log aM.data.N)*aM.data.g z)
  let V := 4*(S z-S a)/(aM.alpha.val.val a*delta^2*kmin*F)
  let T := 8*(S z-S a)/(aM.alpha.val.val a^2*F)
  let L := z-a
  let I := ∫r in Ioo a z,orderedPathB (n+1) bf hf (aM.alpha.val.val r)-(S r)^2
  have haI : a∈Icc aM.data.rmin 1 := ⟨ha.le,haz.trans hz⟩
  have hzI : z∈Icc aM.data.rmin 1 := ⟨ha.le.trans haz,hz⟩
  have halpha : 0<aM.alpha.val.val a:=m.profile_pos ha (haz.trans hz)
  have hzalpha : 0 ≤ aM.alpha.val.val z := halpha.le.trans (aM.alpha.val.property.2 haz)
  have hy0 : 0 ≤ y := (add_nonneg hxs.le hzalpha).trans hy
  have hL : 0 ≤ L := sub_nonneg.mpr haz
  have hF : 0<F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos aM.data.d (sq_pos_of_pos aM.data.hd) z))
  have hmom:=aM.radius_moments
  have hS : 0 ≤ S z-S a:=sub_nonneg.mpr (hmom.1 haI hzI haz)
  have hV : 0 ≤ V:=by dsimp only [V];positivity
  have hT : 0 ≤ T:=by dsimp only [T];positivity
  have hdef:=m.radiusDefect_tendsto as mesh ho hend hmesh hlim ha.le hz hkmin hfloor
  have Hdefeq j : m.radiusDefect (as j)
      (comparisonRadiusMassWeight m.R m.alpha.val.val (Ioo a z) 1 kmin)=
      ∑i,m.radiusRowMass q (as j) Finset.univ a z i*
        actualCutReplicaDefect (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val
          (physicalPathSecondMoment (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val):=by
    unfold ShiftedNativeBandModel.radiusDefect
    apply Finset.sum_congr rfl
    intro i _
    rw [m.radiusRowMass_eq_duration_weight q (as j) (ho j) (hend j) ha haz hz
      (by norm_num : (0:ℝ) < 1) hkmin hfloor i,one_mul]
  dsimp only at hdef
  simp_rw [Hdefeq] at hdef
  have heta (eta : ℝ) (heta : 0<eta) : I ≤
      comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta) (2*delta) := by
    have hvar:=aM.original_wall_radius_dominated_variance_eventually hN hlog hnd
      dphys e as mesh ho hend hmesh hmesh0 hlim ha haz hz hdelta hkmin
      measurableSet_Ioo (Subset.refl _) hfloor heta
    have hcov:=aM.original_radius_covariance_eventually hN hlog hnd
      dphys e as mesh ho hend hmesh hmesh0 hlim ha haz hz hkmin
      measurableSet_Ioo (Subset.refl _) hfloor heta
    have hfinite : ∀ᶠj in atTop,
        (∑i,m.radiusRowMass q (as j) Finset.univ a z i*
          actualCutReplicaDefect (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val
            (physicalPathSecondMoment (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val)) ≤
        comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta)
          (2*delta+2*(mesh j/m.c)) := by
      filter_upwards [hraw,hvar,hcov] with j hjRaw hjVar hjCov
      let steps := sampleClockSteps q 0 (as j)
      let Q := physicalRawRatio (n+1) 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id
      let mass := m.radiusRowMass q (as j) Finset.univ a z
      let Tj := ∑i,mass i*actualCutCovarianceEnergy (n+1) steps (q 0) i.val
      have hTj0 : 0 ≤ Tj := Finset.sum_nonneg (fun i _=>mul_nonneg
        (m.radiusRowMass_nonneg q (as j) Finset.univ a z i)
        (actualCutCovarianceEnergy_nonneg (n+1) steps (sampleClockSteps_ordered q _ (ho j)) (q 0) i.val))
      have hTj : Tj ≤ T+eta := by
        calc
          _ = ∑i,pathMassDifferences steps 0 i*comparisonOriginalRadiusWeights q (as j)
              (comparisonRadiusMassWeight m.R aM.alpha.val.val (Ioo a z) 1 kmin) i*
              actualCutCovarianceEnergy (n+1) steps (q 0) i.val := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp only [mass]
            rw [m.radiusRowMass_eq_duration_weight q (as j)
              (ho j) (hend j) ha haz hz (by norm_num : (0:ℝ)<1) hkmin hfloor i,one_mul]
          _ ≤ _ := hjCov
      have hheight : Q^2*y ≤ (bins:ℝ)*w :=
        (mul_le_mul_of_nonneg_right hjRaw hy0).trans hwidth
      have hfin := m.radius_height_bin_defect_le (n+1) q
        (as j) (ho j) (hend j) (hmesh j) (hmesh0 j) ha haz hz hxs hy hdelta hw hkmin hfloor
        hbins (by positivity : 0 ≤ V+eta) hheight hjVar
      dsimp only at hfin
      have hfin' : (∑i,mass i*actualCutReplicaDefect (n+1) steps (q 0) i.val
          (physicalPathSecondMoment (n+1) steps (q 0) i.val)) ≤
          comparisonRadiusMeanSquareBudget bins L delta y (Q^2) w (V+eta) Tj (2*delta+2*(mesh j/m.c)) := by
        simpa only [comparisonRadiusMeanSquareBudget,←pow_mul,show 2*2=4 by decide] using hfin
      have hEj : 0 ≤ 2*delta+2*(mesh j/m.c) := by have hmj := hmesh0 j;have hc:=m.hc;positivity
      exact hfin'.trans (comparisonRadiusMeanSquareBudget_raw_covariance_mono bins hL hdelta hy0
        (sq_nonneg Q) hjRaw hTj0 hTj hEj)
    have hEmesh : Tendsto (fun j=>2*delta+2*(mesh j/m.c)) atTop (𝓝 (2*delta)) := by
      simpa only [zero_div,mul_zero,add_zero] using
        (tendsto_const_nhds.add (hlim.div_const m.c |>.const_mul 2))
    have hbudget := ((comparisonRadiusMeanSquareBudget_continuous bins L delta y B w (V+eta) (T+eta)).tendsto
      (2*delta)).comp hEmesh
    exact le_of_tendsto_of_tendsto hdef hbudget hfinite
  have hcont : Continuous (fun eta=>comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta) (2*delta)) := by
    unfold comparisonRadiusMeanSquareBudget
    fun_prop
  have hlimit : Tendsto (fun eta=>comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta) (2*delta))
      (𝓝[>] (0:ℝ)) (𝓝 (comparisonRadiusMeanSquareBudget bins L delta y B w V T (2*delta))) := by
    simpa only [add_zero] using (hcont.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hout : I ≤ comparisonRadiusMeanSquareBudget bins L delta y B w V T (2*delta) := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin] with eta he
    exact heta eta he
  exact hout

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
