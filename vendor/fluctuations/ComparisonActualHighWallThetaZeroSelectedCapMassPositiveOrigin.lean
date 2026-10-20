module

public import ComparisonActualHighWallThetaZeroSelectedCapEndpointsPositiveOrigin
public import ComparisonShiftedNativePositiveOriginMaskColumns

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.retainedCapRows_support_eventually_positive_origin (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin≤ ag) (hzg : zg≤1)
    (bins : ℕ) (hbins : 0< bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hlabel : ∀j,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=b)
    (hat : ag≤(c t).left) (hzt : (c t).right≤ zg)
    {r : ℝ} (hrD : r∉Dcuts) (hrr : r≠(c t).right) :
    let m:=W.shiftedNativeModel
    ∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i))
        (P.retainedCapRows c Dcuts ag zg (as j) bins (w j) t b) ↔r∈Ioo (c t).left (c t).right) := by
  dsimp only
  let m:=W.shiftedNativeModel
  by_cases hr : r∈Ioo (c t).left (c t).right
  · filter_upwards [P.retainedCapRows_cell_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim
      hag hzg bins hbins w hwhole t b hlabel hat hzt hr hrD] with j hj
    obtain ⟨i,hi,_,hri⟩:=hj
    exact ⟨fun _=>hr,fun _=>⟨i,hi,hri⟩⟩
  · by_cases hlo : r≤(c t).left
    · apply Eventually.of_forall
      intro j
      constructor
      · rintro ⟨i,hi,hri⟩
        have hc:=(Finset.mem_filter.mp hi).2
        rw [m.rowRadius_eq_partitionPoint] at hc
        exact False.elim ((not_lt_of_ge hlo) (hc.1.trans hri.1))
      · exact fun h=>False.elim (hr h)
    · have hright : (c t).right< r:=lt_of_le_of_ne
        (le_of_not_gt (fun hh=>hr ⟨lt_of_not_ge hlo,hh⟩)) hrr.symm
      obtain ⟨_,_,_,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
      filter_upwards [(tendsto_order.mp ht).2 (r-(c t).right) (sub_pos.mpr hright)] with j hj
      constructor
      · rintro ⟨i,hi,hri⟩
        have hc:=Finset.mem_filter.mp hi
        have hid:=(P.retainedRows_mem c Dcuts ag zg (as j) i).mp
          (P.retainedBin_subset c Dcuts ag zg (as j) bins (w j) b hc.1)
        have hcI:=hc.2
        rw [m.rowRadius_eq_partitionPoint] at hcI
        have HD:=hdiam j i.val hid.1
        dsimp only at hj HD
        linarith [hri.2,hcI.2]
      · exact fun h=>False.elim (hr h)

theorem Potential.retainedCapRows_mass_tendsto_positive_origin (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin≤ ag) (hzg : zg≤1)
    (bins : ℕ) (hbins : 0< bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hlabel : ∀j,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=b)
    (hat : ag≤(c t).left) (hzt : (c t).right≤ zg) :
    Tendsto (fun j=>physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (as j)) 0
      (P.retainedCapRows c Dcuts ag zg (as j) bins (w j) t b)) atTop
      (𝓝 (W.alpha.val.val (c t).right-W.alpha.val.val (c t).left)) := by
  let m:=W.shiftedNativeModel
  let J:=fun j=>P.retainedCapRows c Dcuts ag zg (as j) bins (w j) t b
  have hrow j i (hi:i∈J j) := (P.retainedRows_mem c Dcuts ag zg (as j) i).mp
    (P.retainedBin_subset c Dcuts ag zg (as j) bins (w j) b (Finset.mem_filter.mp hi).1)
  have hmem : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔
        r∈Ioo (c t).left (c t).right):=by
    have hD : ∀ᵐr : ℝ,r∉Dcuts:=by apply ae_iff.mpr;simpa using Dcuts.measure_zero volume
    filter_upwards [ae_restrict_of_ae hD,ae_restrict_of_ae (volume.ae_ne (c t).right)] with r hrD hrr
    exact P.retainedCapRows_support_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
      bins hbins w hwhole t b hlabel hat hzt hrD hrr
  have H:=m.binary_mass_tendsto_of_support_eventually_positive_origin as ho he J
    (fun j i hi=>(hrow j i hi).1) (fun j i hi=>(hrow j i hi).2.2.2.1) hag hzg
    (fun j i hi=>(hrow j i hi).2.2.2.2.1) (fun j i hi=>(hrow j i hi).2.2.2.2.2)
    (Ioo (c t).left (c t).right) measurableSet_Ioo
    (fun r hr=>⟨hat.trans_lt hr.1,hr.2.trans_le hzt⟩) hmem
  have hac : AbsolutelyContinuousOnInterval W.alpha.val.val (c t).left (c t).right:=by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le (c t).hlt.le] using
      (inverseIntegralConstraints_lipschitz W.data.hm W.data.hM W.alpha.property).mono
        (Icc_subset_Icc (c t).hleft (c t).hright)
  have HE : (∫r in Ioo (c t).left (c t).right,deriv W.alpha.val.val r)=
      W.alpha.val.val (c t).right-W.alpha.val.val (c t).left:=by
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (c t).hlt.le]
    exact hac.integral_deriv_eq_sub
  change Tendsto (fun j=>physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0 (J j)) atTop
    (𝓝 (∫r in Ioo (c t).left (c t).right,deriv W.alpha.val.val r)) at H
  rw [HE] at H
  exact H

theorem Potential.retainedCap_cumulative_gap_positive_origin (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin≤ ag) (hzg : zg≤1)
    (bins : ℕ) (hbins : 0< bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hlabel : ∀j,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=b)
    (hat : ag≤(c t).left) (hzt : (c t).right≤ zg)
    (hinterior : ∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    (f : Icc (0:ℝ) 1→ᵇℝ)
    (hf : Tendsto (fun j=>W.actualCDF (as j) (ho j)
      (P.retainedBin c Dcuts ag zg (as j) bins (w j) b)) atTop (𝓝 f)) :
    comparisonContactLimitCoordinate f (c t).right-comparisonContactLimitCoordinate f (c t).left=
      W.alpha.val.val (c t).right-W.alpha.val.val (c t).left ∧
    comparisonContactLimitCoordinate f (c t).left< comparisonContactLimitCoordinate f (c t).right := by
  let m:=W.shiftedNativeModel
  let C:=fun j=>P.retainedBinCoordinates c Dcuts ag zg (as j) (ho j) bins (w j) b
  let p:=fun j=>P.retainedCapFirst c Dcuts ag zg (as j) bins (w j) t b
  let g:=fun j=>physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0
    (P.retainedCapRows c Dcuts ag zg (as j) bins (w j) t b)
  have hcoords:=P.retainedCap_coordinates_tendsto_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
    bins hbins w hwhole t b hlabel hat hzt hinterior f hf
  have hm:=P.retainedCapRows_mass_tendsto_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
    bins hbins w hwhole t b hlabel hat hzt
  have hn:=P.retainedCapRows_eventually_nonempty_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
    bins hbins w hwhole t b hlabel hat hzt hinterior
  have hge : ∀ᶠj in atTop,(C j).x (((C j).unit (p j)).val+1)-(C j).x ((C j).unit (p j)).val=g j:=by
    filter_upwards [hn] with j hj
    rw [←(C j).mass ((C j).unit (p j)),physicalSelectedUnitMass_eq_window_filter,
      P.retainedCap_unit_filter_eq c Dcuts ag zg (as j) (ho j) bins (w j) hwhole t b hj]
  have hc:= (hcoords.2.sub hcoords.1).congr' hge
  have heq:=tendsto_nhds_unique hc hm
  have hlI : (c t).left∈Icc (0:ℝ) 1:=
    ⟨W.data.hrbounds.1.le.trans (c t).hleft,(c t).hlt.le.trans (c t).hright⟩
  have hzI : (c t).right∈Icc (0:ℝ) 1:=
    ⟨hlI.1.trans (c t).hlt.le,(c t).hright⟩
  have hstrict:=inverseConstraint_strictMonoOn W.data.hc W.data.hk W.data.hkc W.alpha.property
    ⟨(c t).hleft,(c t).hlt.le.trans (c t).hright⟩
    ⟨(c t).hleft.trans (c t).hlt.le,(c t).hright⟩ (c t).hlt
  have HE : comparisonContactLimitCoordinate f (c t).right-comparisonContactLimitCoordinate f (c t).left=
      W.alpha.val.val (c t).right-W.alpha.val.val (c t).left:=by
    simpa only [comparisonContactLimitCoordinate,projIcc_of_mem zero_le_one hlI,
      projIcc_of_mem zero_le_one hzI] using heq
  exact ⟨HE,by linarith⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
