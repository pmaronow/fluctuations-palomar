module

public import ComparisonShiftedNativeRadiusSideDominance
public import ComparisonNativeRadiusMeanSquareAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem radiusRowMass_support_upper {ι : Type}
    (q : ℝ→ι→ℝ≥0) 
    (as : List PositiveMass) (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    {a z : ℝ} (hz : z∈Icc m.rmin 1)
    (i : Fin ((sampleClockSteps q 0 as).length+1))
    (hi : radiusRowMass m q as J a z i≠0) :
    physicalCutMass 0 (sampleClockSteps q 0 as) i.val < m.alpha.val.val z := by
  by_contra hn
  have hr := m.R_monotone (le_of_not_gt hn)
  rw [m.R_inverse hz] at hr
  have he : Ioo a z ∩ Ioc
      (m.R (physicalCutMass 0 (sampleClockSteps q 0 as) i.val))
      (m.R (physicalCutMass 0 (sampleClockSteps q 0 as) (i.val+1)))=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro r h
    exact not_lt_of_ge (hr.trans h.2.1.le) h.1.2
  apply hi
  unfold radiusRowMass
  rw [he]
  split_ifs <;> simp

theorem radiusHeightBins_weighted_partition {ι : Type}
    (q : ℝ→ι→ℝ≥0) (as : List PositiveMass)
    (S D : Fin ((sampleClockSteps q 0 as).length+1)→ℝ) {bins : ℕ} (hbins : 0<bins)
    (w a z : ℝ) :
    (∑b : Fin bins,∑i,radiusRowMass m q as
      (NativeRadiusHeight.bin S Finset.univ w b) a z i*D i)=
      ∑i,radiusRowMass m q as Finset.univ a z i*D i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_mul]
  congr 1
  simp only [radiusRowMass,NativeRadiusHeight.bin,Finset.mem_filter,
    Finset.mem_univ,true_and]
  let b0 : Fin bins := ⟨heightBin bins w (S i),heightBin_lt hbins _ _⟩
  have hb (b : Fin bins) : heightBin bins w (S i)=b.val ↔ b=b0 := by
    constructor
    · intro he;exact Fin.ext he.symm
    · intro he;subst b;rfl
  simp_rw [hb]
  simp

theorem radius_height_bin_defect_le (n : ℕ)
    (q : ℝ→FeatureIndex n→ℝ≥0) 
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh a z xs y delta w kmin V : ℝ}
    (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (ha : m.rmin < a) (haz : a ≤ z) (hz : z ≤ 1) (hxs : 0<xs)
    (hy : xs+m.alpha.val.val z ≤ y) (hd : 0<delta) (hw : 0<w)
    (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ m.k r)
    {bins : ℕ} (hbins : 0<bins) (hV : 0 ≤ V)
    (hheight : (physicalRawRatio n 2 (sampleClockSteps q 0 as) 0 xs
      (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id)^2*y ≤ (bins:ℝ)*w)
    (hvariance : comparisonDominatedRadiusVarianceBound n q as
      (comparisonRadiusMassWeight (m.R)
        m.alpha.val.val (Ioo a z) delta kmin) V) :
    let steps := sampleClockSteps q 0 as
    let Q := physicalRawRatio n 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q 0 k)) id measurable_id
    let mass := radiusRowMass m q as Finset.univ a z
    let T := ∑i,mass i*actualCutCovarianceEnergy n steps (q 0) i.val
    let L := z-a
    let E := 2*delta+2*(mesh/m.c)
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
  let full := radiusRowMass m q as Finset.univ a z
  let mass := fun b:Fin bins=>radiusRowMass m q as
    (NativeRadiusHeight.bin S Finset.univ w b) a z
  let T := ∑i,full i*C i
  let L := z-a
  let E := 2*delta+2*(mesh/m.c)
  let cost := 48*V+6*w^2
  let rest := 256*Q^2*y*Real.sqrt ((1+L/delta)*T)*Real.sqrt L+T+
    Q^4*y^2*E+2*Q^2*y*Real.sqrt T*Real.sqrt E
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered q as ho
  have hf i : 0 ≤ full i := radiusRowMass_nonneg m q as Finset.univ a z i
  have hm0 b i : 0 ≤ mass b i := radiusRowMass_nonneg m q as _ a z i
  have hdom b i : mass b i ≤ full i := radiusRowMass_le_full m q as _ a z i
  have hC i : 0 ≤ C i := actualCutCovarianceEnergy_nonneg n steps hs (q 0) i.val
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _=>mul_nonneg (hf i) (hC i))
  have hL : 0 ≤ L := sub_nonneg.mpr haz
  have hc:=m.hc
  have hE : 0 ≤ E := by dsimp only [E];positivity
  have htotal : (∑i,full i)=L := radiusRowMass_total m q as ho ha.le haz hz
  have hy0 : 0 ≤ y := by
    have halpha : 0 ≤ m.alpha.val.val z := (m.alpha.val.property.1 z).1
    linarith
  have hband b i (hi : mass b i≠0) : xs+physicalCutMass 0 steps i.val ≤ y := by
    have hu := radiusRowMass_support_upper m q as _
      (show z∈Icc m.rmin 1 from ⟨ha.le.trans haz,hz⟩) i hi
    exact (add_le_add_right hu.le xs).trans hy
  have hSm b i (hi : mass b i≠0) : S i∈Icc (0:ℝ) ((bins:ℝ)*w) := by
    have hraw := physicalProfile_second_le_raw_ratio n 2 (by norm_num) steps hs (q 0) hxs (i:=i.val)
      (by have h := i.isLt; change i.val<steps.length+1 at h; omega)
    have hmean0 : 0 ≤ S i := physicalPathSecondMoment_nonneg n steps (q 0) i.val
    exact ⟨hmean0,(hraw.trans (mul_le_mul_of_nonneg_left (hband b i hi) (sq_nonneg Q))).trans hheight⟩
  have hbinMem b i (hi : mass b i≠0) : i∈NativeRadiusHeight.bin S Finset.univ w b := by
    by_contra hn
    apply hi
    simp only [mass,radiusRowMass,hn,ite_false]
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
    have hcoeff i (hi : i∈G) := radiusSideCoefficients_le_full m
      q as ho he (NativeRadiusHeight.bin S Finset.univ w b) ha haz hz hd hkmin hfloor i (hl i hi) (hr i hi)
    have hVL i (hi : i∈G) : selectedScoreVariance n steps (q 0)
        (NativeRadiusSide.leftCoefficient (pathMassDifferences steps 0) (mass b) i) ≤ V := by
      simpa only [selectedScoreVariance] using hvariance _ (hcoeff i hi).1
    have hVR i (hi : i∈G) : selectedScoreVariance n steps (q 0)
        (NativeRadiusSide.rightCoefficient (pathMassDifferences steps 0) (mass b) i) ≤ V := by
      simpa only [selectedScoreVariance] using hvariance _ (hcoeff i hi).2
    have hh := radius_physical_ordered_integrated_defect_le_raw_covariance n steps hs (q 0) (mass b) G
      (hm0 b) (fun i h=>radiusRowMass_zero_of_zero_mass m q as _ a z i h)
      hxs hy0 hd hw.le hV hl hr (hband b) (hdiam b) hVL hVR
    dsimp only at hh
    have heB : (∑i,if i∈G then 0 else mass b i) ≤ E := by
      simpa only [G,E,ite_not] using (radiusRows_strip_budget m q as ho
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
  have hpart := radiusHeightBins_mass_partition m q as
    Finset.univ S hbins w a z
  have hweighted := radiusHeightBins_weighted_partition m q as S D hbins w a z
  change (∑b,∑i,mass b i)=∑i,full i at hpart
  change (∑b,∑i,mass b i*D i)=∑i,full i*D i at hweighted
  rw [hweighted,hpart,htotal] at hsum
  exact hsum

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
