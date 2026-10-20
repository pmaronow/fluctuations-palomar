module

public import ComparisonNativeRadiusDefectLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3500000
attribute [local instance] Classical.propDecidable

def comparisonRadiusMeanSquareBudget (bins : ℕ) (L delta y B w V T E : ℝ) : ℝ :=
  (48*V+6*w^2)*L+(bins:ℝ)*(256*B*y*Real.sqrt ((1+L/delta)*T)*Real.sqrt L+T+
    B^2*y^2*E+2*B*y*Real.sqrt T*Real.sqrt E)

theorem comparisonRadiusMeanSquareBudget_continuous (bins : ℕ) (L delta y B w V T : ℝ) :
    Continuous (fun e=>comparisonRadiusMeanSquareBudget bins L delta y B w V T e) := by
  unfold comparisonRadiusMeanSquareBudget
  fun_prop

theorem comparisonRadiusMeanSquareBudget_raw_covariance_mono (bins : ℕ)
    {L delta y u B w V T Tbar E : ℝ}
    (hL : 0 ≤ L) (hd : 0<delta) (hy : 0 ≤ y) (hu0 : 0 ≤ u) (hu : u ≤ B)
    (hT0 : 0 ≤ T) (hT : T ≤ Tbar) (hE : 0 ≤ E) :
    comparisonRadiusMeanSquareBudget bins L delta y u w V T E ≤
      comparisonRadiusMeanSquareBudget bins L delta y B w V Tbar E := by
  have hB : 0 ≤ B := hu0.trans hu
  have hTb : 0 ≤ Tbar := hT0.trans hT
  have hf : 0 ≤ 1+L/delta := by positivity
  have hN := mul_le_mul hu (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hT hf))
    (Real.sqrt_nonneg _) hB
  have hN' := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ 256*y*Real.sqrt L)
  have hQ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0 hu 2) (by positivity : 0 ≤ y^2*E)
  have hC := mul_le_mul hu (Real.sqrt_le_sqrt hT) (Real.sqrt_nonneg _) hB
  have hC' := mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ 2*y*Real.sqrt E)
  have hh : 256*u*y*Real.sqrt ((1+L/delta)*T)*Real.sqrt L+T+u^2*y^2*E+
      2*u*y*Real.sqrt T*Real.sqrt E ≤
      256*B*y*Real.sqrt ((1+L/delta)*Tbar)*Real.sqrt L+Tbar+B^2*y^2*E+
      2*B*y*Real.sqrt Tbar*Real.sqrt E := by nlinarith
  unfold comparisonRadiusMeanSquareBudget
  exact add_le_add_right (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg bins)) _

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_native_radius_centered_defect_le
    {N d lam a z xs y delta kmin B w : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0<d) (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (ha : 0<a) (haz : a ≤ z) (hz : z ≤ 1) (hxs : 0<xs)
    (hy : xs+α.val.val z ≤ y) (hdelta : 0<delta) (hkmin : 0<kmin)
    (hfloor : ∀r∈Ioo a z,kmin ≤ k r)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))
    {bins : ℕ} (hbins : 0<bins) (hB : 0 ≤ B) (hw : 0<w) (hwidth : B*y ≤ (bins:ℝ)*w)
    (hraw : let q:=comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
      ∀ᶠ j in atTop,(physicalRawRatio (n+1) 2 (sampleClockSteps q 0 (as j)) 0 xs
        (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id)^2 ≤ B) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    let V := 4*(S z-S a)/(α.val.val a*delta^2*kmin*F)
    let T := 8*(S z-S a)/(α.val.val a^2*F)
    (∫r in Ioo a z,orderedPathB (n+1) bf hf (α.val.val r)-(S r)^2) ≤
      comparisonRadiusMeanSquareBudget bins (z-a) delta y B w V T (2*delta) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let V := 4*(S z-S a)/(α.val.val a*delta^2*kmin*F)
  let T := 8*(S z-S a)/(α.val.val a^2*F)
  let L := z-a
  let I := ∫r in Ioo a z,orderedPathB (n+1) bf hf (α.val.val r)-(S r)^2
  have haI : a∈Icc (0:ℝ) 1 := ⟨ha.le,haz.trans hz⟩
  have hzI : z∈Icc (0:ℝ) 1 := ⟨ha.le.trans haz,hz⟩
  have halpha : 0<α.val.val a := by
    have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property (by norm_num) haI ha
    simpa only [α.property.1] using hstrict
  have hzalpha : 0 ≤ α.val.val z := halpha.le.trans (α.val.property.2 haz)
  have hy0 : 0 ≤ y := (add_nonneg hxs.le hzalpha).trans hy
  have hL : 0 ≤ L := sub_nonneg.mpr haz
  have hF : 0<F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM (n+1) (by omega)
    b h hd.ne' hlam.le hlb hb hh hh0 α
  have hS : 0 ≤ S z-S a := sub_nonneg.mpr (hmom.1 haI hzI haz)
  have hV : 0 ≤ V := by dsimp only [V];positivity
  have hT : 0 ≤ T := by dsimp only [T];positivity
  have hclock := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h hd.ne' hlam.le hlb hb hh hh0 α
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn hclock.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn hclock.2.1
  have hdef := comparison_native_radius_defect_tendsto hc hk hkc hm hM n bf hf hbf hhf α
    as mesh ho hend hmesh hlim ha.le haz hz hkmin hfloor
  have heta (eta : ℝ) (heta : 0<eta) : I ≤
      comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta) (2*delta) := by
    have hvar := comparison_native_dominated_radius_variance_eventually hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α as mesh ho hend hmesh hmesh0 hlim
      ha haz hz hdelta hkmin Kb Kh hparent hfield measurableSet_Ioo (Subset.refl _) hfloor heta
    have hcov := comparison_native_original_radius_covariance_eventually hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α as mesh ho hend hmesh hmesh0 hlim
      ha haz hz hkmin Kb Kh hparent hfield measurableSet_Ioo (Subset.refl _) hfloor heta
    have hfinite : ∀ᶠj in atTop,
        (∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM q α (as j) Finset.univ a z i*
          actualCutReplicaDefect (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val
            (physicalPathSecondMoment (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val)) ≤
        comparisonRadiusMeanSquareBudget bins L delta y B w (V+eta) (T+eta)
          (2*delta+2*(mesh j/c)) := by
      filter_upwards [hraw,hvar,hcov] with j hjRaw hjVar hjCov
      let steps := sampleClockSteps q 0 (as j)
      let Q := physicalRawRatio (n+1) 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id
      let mass := comparisonNativeRadiusRowMass hc hk hkc hm hM q α (as j) Finset.univ a z
      let Tj := ∑i,mass i*actualCutCovarianceEnergy (n+1) steps (q 0) i.val
      have hTj0 : 0 ≤ Tj := Finset.sum_nonneg (fun i _=>mul_nonneg
        (comparisonNativeRadiusRowMass_nonneg hc hk hkc hm hM q α (as j) Finset.univ a z i)
        (actualCutCovarianceEnergy_nonneg (n+1) steps (sampleClockSteps_ordered q _ (ho j)) (q 0) i.val))
      have hTj : Tj ≤ T+eta := by
        calc
          _ = ∑i,pathMassDifferences steps 0 i*comparisonOriginalRadiusWeights q (as j)
              (comparisonRadiusMassWeight R α.val.val (Ioo a z) 1 kmin) i*
              actualCutCovarianceEnergy (n+1) steps (q 0) i.val := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp only [mass]
            rw [comparisonNativeRadiusRowMass_eq_duration_weight hc hk hkc hm hM q α (as j)
              (ho j) (hend j) ha.le haz hz (by norm_num : (0:ℝ)<1) hkmin hfloor i,one_mul]
          _ ≤ _ := hjCov
      have hheight : Q^2*y ≤ (bins:ℝ)*w :=
        (mul_le_mul_of_nonneg_right hjRaw hy0).trans hwidth
      have hfin := comparison_native_radius_height_bin_defect_le hc hk hkc hm hM (n+1) q α
        (as j) (ho j) (hend j) (hmesh j) (hmesh0 j) ha.le haz hz hxs hy hdelta hw hkmin hfloor
        hbins (by positivity : 0 ≤ V+eta) hheight hjVar
      dsimp only at hfin
      have hfin' : (∑i,mass i*actualCutReplicaDefect (n+1) steps (q 0) i.val
          (physicalPathSecondMoment (n+1) steps (q 0) i.val)) ≤
          comparisonRadiusMeanSquareBudget bins L delta y (Q^2) w (V+eta) Tj (2*delta+2*(mesh j/c)) := by
        simpa only [comparisonRadiusMeanSquareBudget,←pow_mul,show 2*2=4 by decide] using hfin
      have hEj : 0 ≤ 2*delta+2*(mesh j/c) := by have hmj := hmesh0 j;positivity
      exact hfin'.trans (comparisonRadiusMeanSquareBudget_raw_covariance_mono bins hL hdelta hy0
        (sq_nonneg Q) hjRaw hTj0 hTj hEj)
    have hEmesh : Tendsto (fun j=>2*delta+2*(mesh j/c)) atTop (𝓝 (2*delta)) := by
      simpa only [zero_div,mul_zero,add_zero] using
        (tendsto_const_nhds.add (hlim.div_const c |>.const_mul 2))
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

end
end OAI.SKFluctuations.LaplaceWindowFormalization
