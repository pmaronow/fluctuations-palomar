module

public import ComparisonNativeOverlapRawAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3800000
attribute [local instance] Classical.propDecidable

structure NativeActualCapInterval (m : NativeBandModel) where
  a : ℝ
  z : ℝ
  ha : 0≤ a
  haz : a< z
  hz : z≤1
  negative : ∀r∈Ioo a z,m.H r<0

abbrev nativeCapTravel (m : NativeBandModel) : ℝ :=
  (m.Lcap/m.N^m.delta)*Real.log ((1+m.U)/m.U)

theorem actual_native_cap_travel (m : NativeBandModel) (c : NativeActualCapInterval m) :
    c.z-c.a≤ nativeCapTravel m := by
  have hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→m.H r<0→deriv m.alpha.val.val r=
      comparisonCap m.N m.delta m.U m.Lcap m.E m.d (m.alpha.val.val r) := by
    filter_upwards [m.hbang] with r hr hr01 hrH
    simpa only [congrFun m.hMdef (m.alpha.val.val r)] using hr hr01 hrH
  exact (potential_comparison_cap_interval_travel (zero_lt_one.trans_le m.hN) m.hU m.hLcap m.hE m.hd
    (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property)
    (fun r _=>m.alpha.val.property.1 r) hbang c.ha c.hz c.haz.le c.negative).2.1

theorem native_actual_inverse_slice_mass (m : NativeBandModel) {a z : ℝ}
    (ha : 0≤ a) (haz : a≤ z) (hz : z≤1) :
    (∫r in Ioo a z,deriv m.alpha.val.val r)=m.alpha.val.val z-m.alpha.val.val a := by
  have hac : AbsolutelyContinuousOnInterval m.alpha.val.val a z := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le haz] using
      (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property).mono (Icc_subset_Icc ha hz)
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le haz,hac.integral_deriv_eq_sub]

theorem actual_native_cap_endpoint_mass_envelope (m : NativeBandModel)
    (c : NativeActualCapInterval m) {cl cu Az z0 : ℝ}
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0≤ Az*m.xs) (htravel : nativeCapTravel m≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r ∧ m.alpha.val.val r≤ cu*r) :
    m.alpha.val.val c.z≤ cu*(m.alpha.val.val c.a/cl+(Az+1)*m.xs) := by
  have hlen := (actual_native_cap_travel m c).trans htravel
  have ha0 : 0≤ m.alpha.val.val c.a := (m.alpha.val.property.1 c.a).1
  have hmax : m.alpha.val.val c.z≤ cu*(max c.a z0+m.xs) := by
    by_cases hz:z0≤ c.z
    · have hh := (hregular c.z ⟨hz,c.hz⟩).2
      have hb := mul_le_mul_of_nonneg_left
        (show c.z≤ max c.a z0+m.xs by linarith [le_max_left c.a z0]) hcu.le
      exact hh.trans hb
    · have hh : m.alpha.val.val c.z≤ m.alpha.val.val z0 := m.alpha.val.property.2 (le_of_not_ge hz)
      have hr := (hregular z0 ⟨le_rfl,hz0.2⟩).2
      exact (hh.trans hr).trans (mul_le_mul_of_nonneg_left
        (by linarith [le_max_right c.a z0,m.hxs] : z0≤ max c.a z0+m.xs) hcu.le)
  have hrad : max c.a z0≤ m.alpha.val.val c.a/cl+Az*m.xs := by
    by_cases ha:z0≤ c.a
    · rw [max_eq_left ha]
      have hp := (hregular c.a ⟨ha,c.haz.le.trans c.hz⟩).1
      have hh : c.a≤ m.alpha.val.val c.a/cl := (le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using hp)
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hAz m.hxs.le))
    · rw [max_eq_right (le_of_not_ge ha)]
      exact hzxs.trans (le_add_of_nonneg_left (div_nonneg ha0 hcl.le))
  exact hmax.trans (mul_le_mul_of_nonneg_left (by linarith :
    max c.a z0+m.xs≤ m.alpha.val.val c.a/cl+(Az+1)*m.xs) hcu.le)

theorem actual_native_outer_cap_mass_floor (m : NativeBandModel)
    (c : NativeActualCapInterval m) {cl cu Az z0 : ℝ}
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0≤ Az*m.xs) (htravel : nativeCapTravel m≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r ∧ m.alpha.val.val r≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs≤ m.alpha.val.val c.z) :
    (cl/(2*cu))*m.alpha.val.val c.z≤ m.alpha.val.val c.a := by
  have he := actual_native_cap_endpoint_mass_envelope m c hcl hcu hAz hz0 hzxs htravel hregular
  have hh : m.alpha.val.val c.z≤2*cu*(m.alpha.val.val c.a/cl) := by nlinarith
  have hp := (mul_le_mul_of_nonneg_right hh hcl.le)
  have hcancel : (m.alpha.val.val c.a/cl)*cl=m.alpha.val.val c.a := div_mul_cancel₀ _ hcl.ne'
  rw [mul_assoc,hcancel] at hp
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) hcu)).mpr
  nlinarith

theorem nativeBroadSlice_scale_le_cap_mass (m : NativeBandModel) (g : NativeBroadSliceGeometry m) :
    g.scale≤ m.alpha.val.val g.capZ := by
  have hh := g.hmass
  rw [native_actual_inverse_slice_mass m (m.hag.le.trans g.haGroup) g.hab.le
    (g.hbGroup.trans m.hzg)] at hh
  have hm := m.alpha.val.property.2 g.hbCap
  have hp := (m.alpha.val.property.1 g.a).1
  linarith

theorem actual_native_outer_broad_cap_local_travel (m : NativeBandModel)
    (g : NativeBroadSliceGeometry m) {cl cu Az z0 : ℝ}
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hz0 : z0∈Icc (0:ℝ) 1)
    (hzxs : z0≤ Az*m.xs) (htravel : nativeCapTravel m≤ m.xs)
    (hregular : ∀r∈Icc z0 1,cl*r≤ m.alpha.val.val r ∧ m.alpha.val.val r≤ cu*r)
    (houter : 2*cu*(Az+1)*m.xs≤ m.alpha.val.val g.capZ) :
    g.capZ-g.capA≤(32*cu^3/cl^3)*m.E/(m.N^m.delta*m.d^3*g.scale) := by
  let c : NativeActualCapInterval m := ⟨g.capA,g.capZ,g.ha,g.haz,g.hz,g.hnegative⟩
  have hfloor := actual_native_outer_cap_mass_floor m c hcl hcu hAz hz0 hzxs htravel hregular houter
  have hvB := nativeBroadSlice_scale_le_cap_mass m g
  have hv : 0< g.scale := m.hU.trans_le g.hscale
  have hAmax : m.alpha.val.val g.capA≤4*g.scale :=
    ((m.alpha.val.property.2 g.haCap).trans (m.alpha.val.property.2 g.hab.le)).trans
      (g.hceilingMass.trans g.hcomparable)
  have hBmax : m.alpha.val.val g.capZ≤(8*cu/cl)*g.scale := by
    have hh := hfloor.trans hAmax
    have hc : 0< cl/(2*cu) := div_pos hcl (mul_pos (by norm_num) hcu)
    have hb : m.alpha.val.val g.capZ≤(4*g.scale)/(cl/(2*cu)) :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)
    convert hb using 1
    field_simp [hcl.ne',hcu.ne']
    <;> ring
  let vfloor := (cl/(2*cu))*g.scale
  have hvf : 0< vfloor := mul_pos (div_pos hcl (mul_pos (by norm_num) hcu)) hv
  have hvfa : vfloor≤ m.alpha.val.val g.capA+m.U := by
    have hh := (mul_le_mul_of_nonneg_left hvB (div_pos hcl (mul_pos (by norm_num) hcu)).le).trans hfloor
    exact hh.trans (le_add_of_nonneg_right m.hU.le)
  have hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→m.H r<0→deriv m.alpha.val.val r=
      comparisonCap m.N m.delta m.U m.Lcap m.E m.d (m.alpha.val.val r) := by
    filter_upwards [m.hbang] with r hr hr01 hrH
    simpa only [congrFun m.hMdef (m.alpha.val.val r)] using hr hr01 hrH
  have ht := (potential_comparison_cap_interval_travel (zero_lt_one.trans_le m.hN)
    m.hU m.hLcap m.hE m.hd (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property)
    (fun r _=>m.alpha.val.property.1 r) hbang g.ha g.hz g.haz.le g.hnegative).2.2
      vfloor hvf hvfa
  have hA0 := (m.alpha.val.property.1 g.capA).1
  have hwidth : m.alpha.val.val g.capZ-m.alpha.val.val g.capA≤(8*cu/cl)*g.scale := by linarith
  have hNpos : 0< m.N^m.delta := Real.rpow_pos_of_pos (zero_lt_one.trans_le m.hN) _
  have hscaled := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwidth m.hE.le)
    (mul_nonneg (mul_nonneg hNpos.le (pow_nonneg m.hd.le 3)) (sq_nonneg vfloor))
  have hNpow : m.N^m.delta≠0 := hNpos.ne'
  exact ht.trans (by
    convert hscaled using 1
    dsimp [vfloor]
    field_simp [hNpow,m.hd.ne',hv.ne',hcl.ne',hcu.ne']
    <;> ring)

end OAI.SKFluctuations.LaplaceWindowFormalization
