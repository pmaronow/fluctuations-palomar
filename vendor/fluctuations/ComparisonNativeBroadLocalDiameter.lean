module

public import ComparisonNativeWholeCapEndpointGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4200000
attribute [local instance] Classical.propDecidable

abbrev nativeBroadChosenDiameter (m : NativeBandModel) (s : NativeBandRefinement m)
    (D : ℝ) (j : ℕ) : ℝ := D+2*(s.mesh j*m.Cnode)

theorem nativeBroadChosenDiameter_nonneg (m : NativeBandModel) (s : NativeBandRefinement m)
    {D : ℝ} (hD : 0≤ D) (j : ℕ) : 0≤ nativeBroadChosenDiameter m s D j :=
  add_nonneg hD (mul_nonneg (by norm_num) (mul_nonneg (s.hm0 j) m.Cnode_nonneg))

theorem nativeBroadChosenDiameter_tendsto (m : NativeBandModel) (s : NativeBandRefinement m)
    (D : ℝ) : Tendsto (nativeBroadChosenDiameter m s D) atTop (𝓝 D) := by
  simpa only [nativeBroadChosenDiameter,mul_zero,zero_mul,add_zero] using
    ((s.hmesh.mul_const m.Cnode).const_mul 2).const_add D

namespace NativeBroadFrame

theorem sampled_increment_with_diameter {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (D : ℝ) (hD : 0< D)
    (hcap : 9*Real.log m.N*(f.capZ-f.capA)≤ D) (j : ℕ) {i t : Fin ((s.steps j).length+1)}
    (hi : i∈f.selected j) (ht : t∈f.selected j) (hit : i.val≤ t.val) :
    physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val≤ nativeBroadChosenDiameter m s D j := by
  have hmass := partitionPoint_mono (s.as j) (s.ho j) hit
  have hrad := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha hmass
  have hinc := actual_variableEndpoint_comparison_cap_increment_endpoint_cases
    m.hc m.hk m.hkc m.hm m.hM m.hN m.hlog m.hd m.hnd m.hlam m.hld (m.n+1) (by omega)
    m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha m.H m.multiplier m.hH m.hJ m.hD f.ha f.hz
    (f.hcapRows j i hi) (f.hcapRows j t ht) hrad f.hboundary f.hnegative
  have hleft := comparison_nativeCutMass_lowerRadius m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (s.ho j) (f.selected j) (f.hleft j)
  have hui : 0< partitionPoint 0 (s.as j) i.val := by
    have hh := m.rho_pos.trans_le (hleft i hi)
    simpa only [NativeBandRefinement.steps,
      physicalCutMass_sampleClockSteps m.q 0 (s.as j) i.val (by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)] using hh
  have hut : 0< partitionPoint 0 (s.as j) t.val := hui.trans_le hmass
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have herr := physicalSampledNodeSecondMoment_increment_le m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (s.as j) (s.ho j) (s.he j) (s.hm j)
    (by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)
    (by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ t.isLt) hui hut
  rw [←comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha
    (partitionPoint_mem (s.as j) (s.ho j) i.val),
    ←comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha
    (partitionPoint_mem (s.as j) (s.ho j) t.val)] at herr
  dsimp only [nativeBroadChosenDiameter,NativeBandModel.Cnode,
    NativeBandModel.bf,NativeBandModel.hf,NativeBandModel.q,comparisonNativeCompletedClock,
    NativeBandRefinement.steps] at *
  linarith

theorem sampled_oscillation_with_diameter {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (D : ℝ) (hD : 0< D)
    (hcap : 9*Real.log m.N*(f.capZ-f.capA)≤ D) (j : ℕ) {i t : Fin ((s.steps j).length+1)}
    (hi : i∈f.selected j) (ht : t∈f.selected j) :
    |physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val|≤ nativeBroadChosenDiameter m s D j := by
  have ho := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  rcases le_total i.val t.val with hit|hti
  · rw [abs_of_nonneg (sub_nonneg.mpr
      (physicalPathSecondMoment_mono _ _ ho _ hit (by simpa only [NativeBandRefinement.steps] using Nat.le_of_lt_succ t.isLt)))]
    exact f.sampled_increment_with_diameter D hD hcap j hi ht hit
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr
      (physicalPathSecondMoment_mono _ _ ho _ hti (by simpa only [NativeBandRefinement.steps] using Nat.le_of_lt_succ i.isLt)))]
    exact f.sampled_increment_with_diameter D hD hcap j ht hi hti

theorem sampled_reverse_with_diameter {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (D : ℝ) (hD : 0< D)
    (hcap : 9*Real.log m.N*(f.capZ-f.capA)≤ D) (j : ℕ) {i t : Fin ((s.steps j).length+1)}
    (hi : i∈f.selected j) (ht : t∈f.selected j) (hit : i.val≤ t.val) :
    physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val≤ m.reverse (nativeBroadChosenDiameter m s D j) := by
  have ho := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  have hbase : 0≤ physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val :=
    sub_nonneg.mpr (physicalPathSecondMoment_mono _ _ ho _ hit (by simpa only [NativeBandRefinement.steps] using Nat.le_of_lt_succ t.isLt))
  have hlR : (2:ℝ)< m.l := by exact_mod_cast m.hl
  have hp : 0≤((m.l:ℝ)-2)/((m.l:ℝ)-1) := div_nonneg (by linarith) (by linarith)
  have hd := Real.rpow_le_rpow hbase (f.sampled_increment_with_diameter D hD hcap j hi ht hit) hp
  have hn := physical_movement_fourth_le_raw_interpolation (m.n+1) m.l m.hl
    (s.steps j) ho (m.q 0) m.hxs hit (by omega)
  have hraw0 : 0≤ physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id :=
    zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hmass0 : 0≤ m.xs+physicalCutMass 0 (s.steps j) t.val :=
    add_nonneg m.hxs.le (physicalCutMass_mem _ ho _).1
  have hrawPower := pow_le_pow_left₀ (mul_nonneg (by norm_num) hraw0)
    (mul_le_mul_of_nonneg_left (f.rawUpper j) (by norm_num : (0:ℝ)≤2)) (2*m.l)
  have hmassPower := pow_le_pow_left₀ hmass0 (f.hmassUpper j t ht) m.l
  have hprod := mul_le_mul hrawPower hmassPower (pow_nonneg hmass0 _)
    (pow_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans m.hQ)) _)
  have hrp := Real.rpow_le_rpow
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hraw0) _) (pow_nonneg hmass0 _))
    hprod (div_nonneg zero_le_one (by linarith : 0≤(m.l:ℝ)-1))
  have hfinal := mul_le_mul hd hrp (Real.rpow_nonneg
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hraw0) _) (pow_nonneg hmass0 _)) _)
    (Real.rpow_nonneg (nativeBroadChosenDiameter_nonneg m s hD.le j) _)
  exact hn.trans (by simpa only [NativeBandModel.reverse] using hfinal)

theorem finite_budget_with_diameter {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (D : ℝ) (hD : 0< D)
    (hcap : 9*Real.log m.N*(f.capZ-f.capA)≤ D) (hcut : 0< cut) (j : ℕ) :
    f.defect j≤ nativeConditionalLedgerBudget 1 (f.widths j) cut (nativeBroadChosenDiameter m s D j)
      (f.sideFilled j) (f.unionFilled j) (m.reverse (nativeBroadChosenDiameter m s D j)) m.Lside := by
  have ho := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  have hp : 0< f.widths j := by linarith [f.hwidths j]
  have hpoints := f.point_geometry hcut j
  have hc := comparisonNativeWeightedCovarianceEnergy_le_integral
    m.hc m.hk m.hkc m.hm m.hM m.n m.dphys m.e m.d m.lam m.b m.h m.alpha
    (s.as j) (s.ho j) (s.he j) (s.hm j) (s.hm0 j) (f.selected j)
    (fun _=>(0:Fin 1)) (fun _=>1) (fun _=>by norm_num) (by norm_num : (0:ℝ)≤1)
    (fun _=>le_rfl) m.hcut m.hcut1 (f.hleft j)
  dsimp only at hc
  rw [nativeWeightedCovarianceEnergy_one] at hc
  simp only [mul_one] at hc
  change (∑i,physicalSelectedCellMass (s.steps j) (f.selected j) i*
    actualCutCovarianceEnergy (m.n+1) (s.steps j) (m.q 0) i.val)≤ f.unionFilled j at hc
  have hT0 : 0≤ f.unionFilled j := (Finset.sum_nonneg (fun i _=>mul_nonneg
    (physicalSelectedCellMass_nonneg _ ho _ i)
    (actualCutCovarianceEnergy_nonneg _ _ ho _ _))).trans hc
  let tauC := f.unionFilled j/f.widths j
  have htau0 : 0≤ tauC := div_nonneg hT0 hp.le
  have htau : f.widths j*tauC=f.unionFilled j := by dsimp [tauC];field_simp [hp.ne']
  have hv := physical_actual_bin_variance_le_native_integral
    m.hc m.hk m.hkc m.hm m.hM m.n m.dphys m.e m.d m.lam m.b m.h m.alpha
    (s.as j) (s.ho j) (s.he j) (s.hm j) (s.hm0 j) (f.selected j) (fun _=>(0:Fin 1))
    (nativeBroadPoints (f.widths j)) hpoints.1 hpoints.2.1 hcut (f.hwidths j)
    hpoints.2.2.1 m.hcut m.hcut1 (f.hleft j)
  dsimp only at hv
  change actualBinSideVariance (m.n+1) 1 (s.steps j) (m.q 0) (f.selected j)
    (fun _=>(0:Fin 1)) (nativeBroadPoints (f.widths j)) cut (f.widths j)≤ f.sideFilled j at hv
  have hreverseL : ∀bb:Fin 1,∀i t:Fin ((s.steps j).length+1),i.val< t.val→
      fineCoupling (physicalSelectedCellMass (s.steps j) (f.selected j)) (fun _=>(0:Fin 1))
        (fun u v=>coarseLeft (nativeBroadPoints (f.widths j)) 0 cut (f.widths j-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val≤ m.reverse (nativeBroadChosenDiameter m s D j) := by
    intro bb i t hit hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    exact f.sampled_reverse_with_diameter D hD hcap j hi ht hit.le
  have hreverseR : ∀bb:Fin 1,∀i t:Fin ((s.steps j).length+1),t.val< i.val→
      fineCoupling (physicalSelectedCellMass (s.steps j) (f.selected j)) (fun _=>(0:Fin 1))
        (fun u v=>coarseRight (nativeBroadPoints (f.widths j)) (f.widths j) cut (f.widths j-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val≤ m.reverse (nativeBroadChosenDiameter m s D j) := by
    intro bb i t hti hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    rw [physicalSideMovementMoment_comm _ _ _ i.val t.val]
    exact f.sampled_reverse_with_diameter D hD hcap j ht hi hti.le
  have hn := physical_selected_bins_defect_le_variance_budget (v:=f.widths j) (m.n+1) 1 (s.steps j) ho (m.q 0)
    (fun _=>1) (fun _=>f.selected j) (fun _ _=>(0:Fin 1))
    (fun _=>nativeBroadPoints (f.widths j)) (fun _=>f.widths j)
    (fun _=>hpoints.1) (fun _=>hpoints.2.1) hcut (fun _=>f.hwidths j)
    (fun _=>hpoints.2.2.1) (fun _=>hpoints.2.2.2) (nativeBroadChosenDiameter_nonneg m s hD.le j) htau0
    (m.reverse_nonneg (nativeBroadChosenDiameter_nonneg m s hD.le j)) m.hLside (fun _=>f.hsideLog j)
    (by simp) (fun _ i hi t ht=>f.sampled_oscillation_with_diameter D hD hcap j hi ht)
    (by simpa using hv) (by simpa only [Fin.sum_univ_one,htau] using hc) hreverseL hreverseR
  dsimp only at hn
  rw [actualBinsVarianceBudget_native_expansion,htau] at hn
  simpa only [Fin.sum_univ_one,defect] using hn

theorem thermal_le_native_budget_with_diameter {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (D : ℝ) (hD : 0< D)
    (hcap : 9*Real.log m.N*(f.capZ-f.capA)≤ D) (hcut : 0< cut) :
    (∫u in 0..1,f.slice.indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget 1 f.width cut D
        (f.AS/(m.P*m.rho)*Real.log (f.width/cut))
        (f.AC*f.width/(m.P*m.rho^2)) (m.reverse D) m.Lside := by
  let VS := f.AS/(m.P*m.rho)*Real.log (f.width/cut)
  let TC := f.AC*f.width/(m.P*m.rho^2)
  let C := 66+64*m.Lside+65536*(1+m.Lside)^2
  have hC : 0≤ C := by have hL:=m.hLside;dsimp [C];positivity
  have hdiam := nativeBroadChosenDiameter_tendsto m s D
  have hrev : Tendsto (fun j=>m.reverse (nativeBroadChosenDiameter m s D j)) atTop (𝓝 (m.reverse D)) :=
    (hdiam.rpow_const (Or.inl hD.ne')).mul_const _
  apply le_of_forall_pos_le_add
  intro t ht
  let err := t/(48+C+1)
  have herr : 0< err := div_pos ht (by linarith)
  have hv := f.sideFilled_eventually hcut herr
  have hc := f.unionFilled_eventually herr
  have hupper : ∀ᶠ j in atTop,f.defect j≤ nativeConditionalLedgerBudget 1 (f.widths j) cut
      (nativeBroadChosenDiameter m s D j) (VS+err) (TC+err) (m.reverse (nativeBroadChosenDiameter m s D j)) m.Lside := by
    filter_upwards [hv,hc] with j hvj hcj
    have hn := f.finite_budget_with_diameter D hD hcap hcut j
    unfold nativeConditionalLedgerBudget at hn ⊢
    have hT : C*f.unionFilled j≤ C*(TC+err) :=
      mul_le_mul_of_nonneg_left (by simpa only [div_mul_eq_mul_div] using hcj) hC
    have hV : 48*f.sideFilled j≤48*(VS+err) :=
      mul_le_mul_of_nonneg_left hvj (by norm_num : (0:ℝ)≤48)
    exact hn.trans (add_le_add (add_le_add (add_le_add (add_le_add hV le_rfl) le_rfl) hT) le_rfl)
  have hlimUpper : Tendsto (fun j=>nativeConditionalLedgerBudget 1 (f.widths j) cut
      (nativeBroadChosenDiameter m s D j) (VS+err) (TC+err) (m.reverse (nativeBroadChosenDiameter m s D j)) m.Lside) atTop
      (𝓝 (nativeConditionalLedgerBudget 1 f.width cut D (VS+err) (TC+err)
        (m.reverse D) m.Lside)) := by
    unfold nativeConditionalLedgerBudget
    exact (((tendsto_const_nhds.add
      ((f.hwidthlim.const_mul _).mul (hdiam.pow 2))).add
      ((f.hwidthlim.const_mul 32).mul hrev)).add tendsto_const_nhds).add tendsto_const_nhds
  have hlimit := le_of_tendsto_of_tendsto f.defect_tendsto hlimUpper hupper
  have herrbound : (48+C)*err≤ t := by
    dsimp [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<48+C+1)).mpr
    nlinarith
  dsimp only [VS,TC] at hlimit
  unfold nativeConditionalLedgerBudget at hlimit ⊢
  dsimp only [C] at herrbound
  nlinarith

end NativeBroadFrame

abbrev nativeOuterBroadTravel (m : NativeBandModel) (g : NativeBroadSliceGeometry m)
    (cl cu : ℝ) : ℝ :=
  min (nativeCapTravel m) ((32*cu^3/cl^3)*m.E/(m.N^m.delta*m.d^3*g.scale))

abbrev nativeOuterBroadDiameter (m : NativeBandModel) (g : NativeBroadSliceGeometry m)
    (cl cu : ℝ) : ℝ := 9*Real.log m.N*nativeOuterBroadTravel m g cl cu

theorem nativeCapTravel_pos (m : NativeBandModel) : 0< nativeCapTravel m := by
  have hratio : 1<(1+m.U)/m.U := (lt_div_iff₀ m.hU).mpr (by linarith)
  exact mul_pos (div_pos m.hLcap (Real.rpow_pos_of_pos (zero_lt_one.trans_le m.hN) _))
    (Real.log_pos hratio)

theorem nativeOuterBroadDiameter_pos (m : NativeBandModel) (g : NativeBroadSliceGeometry m)
    {cl cu : ℝ} (hcl : 0< cl) (hcu : 0< cu) : 0< nativeOuterBroadDiameter m g cl cu := by
  have hv : 0< g.scale := m.hU.trans_le g.hscale
  have hNp : 0< m.N^m.delta := Real.rpow_pos_of_pos (zero_lt_one.trans_le m.hN) _
  have hlocal : 0<(32*cu^3/cl^3)*m.E/(m.N^m.delta*m.d^3*g.scale) :=
    div_pos (mul_pos (div_pos (mul_pos (by norm_num) (pow_pos hcu 3)) (pow_pos hcl 3)) m.hE)
      (mul_pos (mul_pos hNp (pow_pos m.hd 3)) hv)
  exact mul_pos (mul_pos (by norm_num) (by linarith [m.hlog] : 0< Real.log m.N))
    (lt_min (nativeCapTravel_pos m) hlocal)

theorem actual_native_outer_broad_slice_comparison
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cl cu Az z0 : ℝ}
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0≤ Az*m.xs) (htravel : nativeCapTravel m≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r ∧ m.alpha.val.val r≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs≤ m.alpha.val.val g.capZ)
    (hstrict : ∀j,∀i<(s.as j).length,
      partitionPoint 0 (s.as j) i< partitionPoint 0 (s.as j) (i+1))
    {cut : ℝ} (hcut : 0< cut) (hsmall : 2*cut< m.U)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
    let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
    let D := nativeOuterBroadDiameter m g cl cu
    (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget 1 width cut D
        (108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))
        (54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2)) (m.reverse D) m.Lside := by
  dsimp only
  obtain ⟨N,hN⟩ := eventually_atTop.mp hraw
  let st := s.tail N
  obtain ⟨j,f,hs,hA,hZ,hscale,hwidth⟩ := exists_actual_native_broad_slice_frame m st g
    (fun t=>hstrict (t+N)) hcut (hsmall.trans_le (g.hscale.trans g.hmass)) hleft hupper hlog
    (fun t=>hN (t+N) (by omega))
  let c : NativeActualCapInterval m := ⟨g.capA,g.capZ,g.ha,g.haz,g.hz,g.hnegative⟩
  have hglobal := actual_native_cap_travel m c
  have hlocal := actual_native_outer_broad_cap_local_travel m g hcl hcu hAz hz0 hzxs htravel
    hregular houter
  have hcap : 9*Real.log m.N*(f.capZ-f.capA)≤ nativeOuterBroadDiameter m g cl cu := by
    rw [hA,hZ]
    exact mul_le_mul_of_nonneg_left (le_min hglobal hlocal)
      (by linarith [m.hlog] : 0≤9*Real.log m.N)
  have hn := f.thermal_le_native_budget_with_diameter (nativeOuterBroadDiameter m g cl cu)
    (nativeOuterBroadDiameter_pos m g hcl hcu) hcap hcut
  simpa only [NativeBroadFrame.AS,NativeBroadFrame.AC,NativeBroadFrame.loss,hs,hscale,hwidth] using hn

end OAI.SKFluctuations.LaplaceWindowFormalization
