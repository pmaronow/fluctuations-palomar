module

public import ComparisonNativeOuterBroadPhysicalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

theorem actual_native_outer_broad_error_eventually
    {delta margin gamma Q C K Cg Cscale J cl cu Az Ccut Ko R V0 : ℝ}
    (hdelta : 0 < delta) (hmargin : 0 ≤ margin) (hgamma : 0 < gamma)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hCg : 0 ≤ Cg) (hCscale : 0 ≤ Cscale)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hAz : 0 ≤ Az)
    (hJ9 : 9 ≤ J) (hJlarge : (288*cu^3/cl^3)*Cscale ≤ J)
    (hcut : 3 ≤ Ccut) (hKo : 0 ≤ Ko) (hR : 0 ≤ R) (hV0 : 0 ≤ V0) :
    ∀ᶠ N : ℝ in atTop, ∀ (m : NativeBandModel) (g : NativeBroadSliceGeometry m) (z0 : ℝ),
      m.N=N → m.delta=delta → m.Q=Q →
      NativeOrdinaryPhysicalData m Ccut Ko 64 V0 → NativeBandRawMaster m →
      z0∈Icc (0:ℝ) 1 → z0 ≤ Az*m.xs → nativeCapTravel m ≤ m.xs →
      (∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ cu*r) →
      2*cu*(Az+1)*m.xs ≤ m.alpha.val.val g.capZ →
      g.scale ≤ R*m.rho → g.scale ≤ 1 → m.xs ≤ m.bandMass → m.bandMass ≤ Cscale*g.scale →
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r) ≤ m.bandMass →
      m.N^(-(1:ℝ)) ≤ m.Lcap → m.U ≤ m.bandMass →
      gamma*m.N^(-(2:ℝ)/3+margin)*m.d ≤ m.E →
      m.y ≤ C*m.bandMass → m.bandMass ≤ Cg*m.ag →
      m.N*m.groupStrength ≤ K*m.P → (m.delta+2)/((m.l:ℝ)-1) ≤ delta →
      (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
        N^(4*delta)*m.E := by
  have hJ0 : 0 ≤ J := by linarith
  have hCcut : 0 ≤ Ccut := by linarith
  have hF := comparison_log_loss_eventually (C:=324+192*Ccut) (p:=1) (by positivity) hdelta
  have hthree := comparison_log_loss_eventually (C:=3) (p:=0) (by norm_num) hdelta
  filter_upwards [native_broad_trace_coefficient_eventually (S:=Ccut) hdelta hKo hK hR hCcut,
    comparison_outer_error_core_eventually (Q:=Q) hdelta hmargin hgamma hC hK hJ0
      (show 0 ≤ 2*Cg by positivity),
    comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=V0) (by norm_num) hV0 hcut,
    hF,hthree,eventually_ge_atTop (4:ℝ)] with N htrace hcore hrestore hFpow h3pow hN4
  intro m g z0 hNeq hdeq hQeq data hraw hz0 hzxs htravel hregular houter
    hratio hscale1 hxv hvb hwb hLlower hvU hlower hyv hgeom hstrength horder
  have hN : 1 ≤ N := by linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hcutoff := comparison_physical_cutoff_log (C:=Ccut) hNp
  have hlogcut : Real.log (1/N^(-Ccut)) ≤ m.Lside := by rw [hcutoff.2,data.side,hNeq]
  have hsmall : 2*N^(-Ccut) < m.U := by
    have hp := Real.rpow_le_rpow_of_exponent_le hN (show -Ccut ≤ -(2:ℝ) by linarith)
    have he : N^(-(2:ℝ))=1/N^2 := by rw [Real.rpow_neg hNp.le,Real.rpow_two,one_div]
    rw [he] at hp
    have hl : 2/N^2 < 1/N := by field_simp; nlinarith
    have hUlo := data.U_lower
    rw [hNeq] at hUlo
    have hp' : 2*N^(-Ccut) ≤ 2/N^2 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ 2 by norm_num)
    exact hp'.trans_lt (hl.trans_le hUlo)
  have hb := actual_native_outer_broad_physical_trace_error m g hraw hcl hcu hAz hz0 hzxs
    htravel hregular houter hcutoff.1 hsmall data.left data.upper hlogcut data.U_eq hK hR hstrength hratio
  dsimp only at hb
  have ht := htrace m.U m.Ko m.Lside K m.hU data.U_le_one
    (hNeq ▸ data.U_lower) (zero_le_one.trans m.hKo) data.Ko_le m.hLside
    (by rw [data.side,hNeq]) hK
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hN hdelta.le) hK)
  have hw := native_broad_slice_mass_bounds m g
  have hw0 := hw.1.le
  let Db := nativeOuterBroadDiameter m g cl cu
  change (∫u in 0..1,(Ioo g.a g.b).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
    3*nativeBroadPhysicalTraceCoefficient m.N (m.Ko^2+1+50*Real.log ((1+m.U)/m.U)) K R m.Lside*m.E+
    (244+192*m.Lside)*m.groupStrength*(∫r in Ioo g.a g.b,deriv m.alpha.val.val r)*Db^2+
    96*m.groupStrength*(∫r in Ioo g.a g.b,deriv m.alpha.val.val r)*m.reverse Db+
    48*m.groupStrength*N^(-Ccut) at hb
  have hDp : 0 < Db := nativeOuterBroadDiameter_pos m g hcl hcu
  have hg := native_outer_broad_diameter_physical_bounds m g hcl hcu hclcu data.d_le_one
    data.U_eq data.U_le_one hLlower data.y_upper htravel hxv hscale1 hCscale hvb hJ9 hJlarge
  have hr := native_outer_broad_remainder_le_core m hw.1.le hwb data.U_eq hvU hgamma hlower
    hC hK hyv hstrength (show 0 ≤ 2*Cg*Real.log m.N by have := m.hlog; positivity)
    (m.groupStrength_mass_budget hCg hgeom) hDp
    (show 0 ≤ J*Real.log m.N by have := m.hlog; positivity)
    (show 0 ≤ J*Real.log m.N by have := m.hlog; positivity)
    hg.1 hg.2.1 hg.2.2 horder
  let F := (324+192*m.Lside)/3
  have hF0 : 0 ≤ F := by dsimp [F]; have := m.hLside; positivity
  have hFN : F ≤ N^delta := by
    have hlg := hNeq ▸ m.hlog
    have hh : 324+192*m.Lside ≤ (324+192*Ccut)*Real.log N := by
      rw [data.side,hNeq]
      nlinarith
    dsimp [F]
    simp only [Real.rpow_one] at hFpow
    have hp : 0 ≤ N^delta := (Real.rpow_pos_of_pos hNp _).le
    apply (div_le_iff₀ (show (0:ℝ) < 3 by norm_num)).mpr
    exact (hh.trans hFpow).trans (by nlinarith only [hp])
  have hmain := hcore m.E F delta m.hE.le hF0 hFN le_rfl
  have hdiam := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 340+192*m.Lside by have := m.hLside; positivity)
  have hrem0 := m.reverse_nonneg hDp.le
  have hrem : 0 ≤ (244+192*m.Lside)*m.groupStrength*
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r)*m.reverse Db := by
    have := m.hLside
    have := m.groupStrength_pos
    positivity
  have hdiam0 : 0 ≤ 96*m.groupStrength*
      (∫r in Ioo g.a g.b,deriv m.alpha.val.val r)*Db^2 := by
    have := m.groupStrength_pos
    positivity
  have hstrengthL : m.groupStrength ≤ m.lam := laplaceComparisonStrength_le m.d m.hlam.le m.ag
  have hc := hrestore m.P m.y m.bandMass m.groupStrength m.E m.P_pos.le
    (by simpa only [one_mul,hNeq] using data.P_le_N) m.hy.le (hNeq ▸ data.y_upper)
    m.hbandMass.le data.mass_upper m.groupStrength_pos.le (hstrengthL.trans data.lam_le_one)
    (hNeq ▸ data.E_lower)
  have hbin : 0 ≤ ((Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3) := by have := m.P_pos; positivity
  have hcutterm : 0 ≤ m.groupStrength*N^(-Ccut) := by have := m.groupStrength_pos; positivity
  have hc' : 48*m.groupStrength*N^(-Ccut) ≤ m.E := by nlinarith
  simp only [hNeq,hdeq,hQeq,mul_assoc] at hr hdiam hb
  have ht' := mul_le_mul_of_nonneg_right ht m.hE.le
  simp only [Real.rpow_zero,mul_one] at h3pow
  have hp23 := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 3*delta by linarith)) m.hE.le
  have hp13 := mul_le_mul_of_nonneg_right (Real.one_le_rpow hN (show 0 ≤ 3*delta by linarith)) m.hE.le
  have hsum := mul_le_mul_of_nonneg_right h3pow (show 0 ≤ N^(3*delta)*m.E by have := m.hE; positivity)
  have he : N^delta*(N^(3*delta)*m.E)=N^(4*delta)*m.E := by
    rw [←mul_assoc,←Real.rpow_add hNp]
    congr 2
    ring
  rw [he] at hsum
  dsimp [F] at hmain
  change (3*((324+192*m.Lside)/3)+16)*comparisonOuterPhysicalCore N delta margin gamma m.E Q C K
    (J*Real.log N) (J*Real.log N) ((2*Cg)*Real.log N) delta ≤ _ at hmain
  simp only [mul_assoc] at hmain
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
