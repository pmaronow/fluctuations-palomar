module

public import ComparisonCanonicalPhysicalStrength
public import ComparisonPhysicalCutoffCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

structure NativeOrdinaryPhysicalData (m : NativeBandModel) (Ccut Ko R V0 : ℝ) : Prop where
  physical : (m.n:ℝ)+1=m.N
  d_le_one : m.d ≤ 1
  E_le_one : m.E ≤ 1
  E_lower : 1/m.N ≤ m.E
  U_eq : m.U=comparisonSmallMass m.N m.E
  U_le_one : m.U ≤ 1
  left : m.cutRadius ≤ m.ag
  upper : m.xs+m.alpha.val.val m.zg ≤ m.y
  mass : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass
  side : m.Lside=Ccut*Real.log m.N
  ratio : m.bandMass/m.rho ≤ R
  Ko_le : m.Ko ≤ Ko
  mass_upper : m.bandMass ≤ V0
  y_upper : m.y ≤ m.N

namespace NativeOrdinaryPhysicalData

theorem lam_le_one {m : NativeBandModel} {Ccut Ko R V0 : ℝ}
    (g : NativeOrdinaryPhysicalData m Ccut Ko R V0) : m.lam ≤ 1 := by
  have hd := m.hd
  nlinarith [m.hld,g.d_le_one]

theorem P_le_N {m : NativeBandModel} {Ccut Ko R V0 : ℝ}
    (g : NativeOrdinaryPhysicalData m Ccut Ko R V0) : m.P ≤ m.N := by
  have he := (laplaceComparisonStrength_le m.d m.hlam.le m.zg).trans g.lam_le_one
  have hN : 0 ≤ m.N := zero_le_one.trans m.hN
  change ((m.n:ℝ)+1)*laplaceComparisonStrength m.d m.lam m.zg ≤ m.N
  rw [g.physical]
  nlinarith

theorem U_lower {m : NativeBandModel} {Ccut Ko R V0 : ℝ}
    (g : NativeOrdinaryPhysicalData m Ccut Ko R V0) : 1/m.N ≤ m.U := by
  rw [g.U_eq]
  unfold comparisonSmallMass
  apply one_div_le_one_div_of_le (mul_pos (zero_lt_one.trans_le m.hN) m.hE)
  have hN : 0 < m.N := zero_lt_one.trans_le m.hN
  nlinarith [g.E_le_one]

theorem loss_nonneg {m : NativeBandModel} {Ccut Ko R V0 : ℝ}
    (_g : NativeOrdinaryPhysicalData m Ccut Ko R V0) :
    0 ≤ nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho := by
  unfold nativeBinScaleLoss
  have hL := m.hLside
  have hAS := m.AS_nonneg
  have hAC := m.AC_nonneg
  have hv := m.hbandMass
  have hr := m.rho_pos
  positivity

end NativeOrdinaryPhysicalData

theorem actual_native_inner_ordinary_error_eventually
    {delta Q C K Ccut Ko R V0 : ℝ}
    (hdelta : 0 < delta) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hcut : 3 ≤ Ccut) (hKo : 0 ≤ Ko) (hR : 0 ≤ R) (hV0 : 0 ≤ V0) :
    ∀ᶠ N : ℝ in atTop, ∀ m : NativeBandModel,
      m.N=N → m.delta=delta → m.Q=Q →
      NativeOrdinaryPhysicalData m Ccut Ko R V0 → NativeBandRawMaster m →
      m.Lcap ≤ m.U → m.N^(-(1:ℝ)) ≤ m.Lcap →
      m.U ≤ comparisonConditionalScale m.N m.delta m.E m.lam →
      m.U ≤ m.bandMass →
      m.bandMass ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam →
      m.y ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam →
      m.N*(m.N^(-m.delta)*m.lam) ≤ K*m.P →
      (m.delta+2)/((m.l:ℝ)-1) ≤ delta →
      (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤ N^(7*delta)*m.E := by
  have hCcut : 0 ≤ Ccut := by linarith
  have hcoef := comparison_log_loss_eventually (C:=K) (p:=0) (zero_le_one.trans hK) hdelta
  have htwo := comparison_log_loss_eventually (C:=2) (p:=0) (by norm_num) hdelta
  filter_upwards [nativeBinScaleLoss_eventually hKo hCcut hR hdelta,
    comparison_capLogFactor_eventually hdelta,
    comparison_inner_error_core_eventually (Q:=Q) hdelta hC,
    comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=V0) (by norm_num) hV0 hcut,
    hcoef,htwo,eventually_ge_atTop (1:ℝ)] with N hF hJ hcore hrestore hKpow h2pow hN
  intro m hNeq hdeq hQeq g hraw hLU hLlower hUA hvU hvA hyA hstrength horder
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hcutoff := comparison_physical_cutoff_log (C:=Ccut) hNp
  have hlogcut : Real.log (1/N^(-Ccut)) ≤ m.Lside := by rw [hcutoff.2,g.side,hNeq]
  have hb := actual_native_inner_ordinary_error_with_strength_distortion m hcutoff.1
    g.left g.upper g.mass hlogcut hraw g.U_eq g.U_le_one hLU hLlower hUA hvU hC
    hvA hyA g.y_upper hK hstrength horder
  let F := nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho
  have hFN : F ≤ N^delta := hF m hNeq g.Ko_le (by rw [g.side,hNeq]) g.ratio
  have hJ1 : m.capLogFactor ≤ 1 := by
    unfold NativeBandModel.capLogFactor
    rw [hNeq,hdeq]
    exact hJ m.U m.hU g.U_le_one (hNeq ▸ g.U_lower)
  have hmain := hcore m.E F m.capLogFactor delta m.hE.le g.loss_nonneg hFN
    m.capLogFactor_nonneg hJ1 le_rfl
  have hcutcost := hrestore m.P m.y m.bandMass m.lam m.E m.P_pos.le
    (by simpa only [one_mul,hNeq] using g.P_le_N) m.hy.le
    (hNeq ▸ g.y_upper) m.hbandMass.le g.mass_upper m.hlam.le g.lam_le_one
    (hNeq ▸ g.E_lower)
  simp only [Real.rpow_zero,mul_one] at hKpow h2pow
  have hDcost : 0 ≤ 16*m.capLogFactor^2*C*N^(2*delta)*m.E := by have hE:=m.hE;positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain (zero_le_one.trans hK)
  have hraise := mul_le_mul_of_nonneg_right hKpow (show 0 ≤ N^(5*delta)*m.E by have hE:=m.hE;positivity)
  have hpow6 : N^delta*(N^(5*delta)*m.E)=N^(6*delta)*m.E := by
    rw [←mul_assoc,←Real.rpow_add hNp]
    congr 2
    ring
  rw [hpow6] at hraise
  have hp6 : 1 ≤ N^(6*delta) := Real.one_le_rpow hN (by linarith)
  have hlast : N^(6*delta)*m.E+m.E ≤ N^(7*delta)*m.E := by
    have hh := mul_le_mul_of_nonneg_right h2pow (show 0 ≤ N^(6*delta)*m.E by have hE:=m.hE;positivity)
    have heq : N^delta*(N^(6*delta)*m.E)=N^(7*delta)*m.E := by
      rw [←mul_assoc,←Real.rpow_add hNp]
      congr 2
      ring
    rw [heq] at hh
    have hE := m.hE
    nlinarith
  rw [hNeq,hdeq,hQeq] at hb
  change (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤
    3*F*K*comparisonInnerPhysicalCore N delta m.E Q C m.capLogFactor delta+
    16*m.capLogFactor^2*C*N^(2*delta)*m.E+
    54*m.lam*(((Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*N^(-Ccut) at hb
  nlinarith

theorem actual_native_outer_ordinary_error_eventually
    {delta margin gamma Q C K Ccap Cscale Cg Ccut Ko R V0 : ℝ}
    (hdelta : 0 < delta) (hmargin : 0 ≤ margin) (hgamma : 0 < gamma)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hCcap : 0 < Ccap) (hCscale : 0 ≤ Cscale)
    (hCg : 0 ≤ Cg) (hcut : 3 ≤ Ccut) (hKo : 0 ≤ Ko) (hR : 0 ≤ R) (hV0 : 0 ≤ V0) :
    ∀ᶠ N : ℝ in atTop, ∀ (m : NativeBandModel) (q : ℝ),
      m.N=N → m.delta=delta → m.Q=Q →
      NativeOrdinaryPhysicalData m Ccut Ko R V0 → NativeBandRawMaster m →
      0 < q → q ≤ m.lo+m.U → m.hi-m.lo ≤ Ccap*q →
      q ≤ Cscale*m.bandMass → m.bandMass ≤ Cscale*q → m.U ≤ m.bandMass →
      gamma*m.N^(-(2:ℝ)/3+margin)*m.d ≤ m.E →
      m.E ≤ m.N^m.delta*m.d^3*q^2 → m.d^3*q ≤ m.localCapFactor Ccap →
      m.y ≤ C*m.bandMass → m.bandMass ≤ Cg*m.ag →
      m.N*m.groupStrength ≤ K*m.P → (m.delta+2)/((m.l:ℝ)-1) ≤ delta →
      (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤ N^(4*delta)*m.E := by
  have hCcut : 0 ≤ Ccut := by linarith
  have hJ : 0 ≤ 9*Ccap*Cscale := by positivity
  have hL : 0 ≤ 2*Cg := by positivity
  have htwo := comparison_log_loss_eventually (C:=2) (p:=0) (by norm_num) hdelta
  filter_upwards [nativeBinScaleLoss_eventually hKo hCcut hR hdelta,
    comparison_outer_error_core_eventually (Q:=Q) hdelta hmargin hgamma hC hK hJ hL,
    comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=V0) (by norm_num) hV0 hcut,
    htwo,eventually_ge_atTop (1:ℝ)] with N hF hcore hrestore h2pow hN
  intro m q hNeq hdeq hQeq g hraw hq hleftmass hspan hscaleL hscaleU hvU hlower hroom hfactor hyv hgeom hstrength horder
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hcutoff := comparison_physical_cutoff_log (C:=Ccut) hNp
  have hlogcut : Real.log (1/N^(-Ccut)) ≤ m.Lside := by rw [hcutoff.2,g.side,hNeq]
  have hb := actual_native_outer_ordinary_error_bound m hcutoff.1 g.left g.upper g.mass
    hlogcut hraw hq hCcap hCscale hleftmass hspan hscaleL hscaleU g.U_eq g.U_le_one hvU
    hgamma hlower hroom hfactor hC hyv g.y_upper hCg hgeom hK hstrength horder
  let F := nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho
  have hFN : F ≤ N^delta := hF m hNeq g.Ko_le (by rw [g.side,hNeq]) g.ratio
  have hmain := hcore m.E F delta m.hE.le g.loss_nonneg hFN le_rfl
  have hs1 : m.groupStrength ≤ 1 :=
    (laplaceComparisonStrength_le m.d m.hlam.le m.ag).trans g.lam_le_one
  have hcutcost := hrestore m.P m.y m.bandMass m.groupStrength m.E m.P_pos.le
    (by simpa only [one_mul,hNeq] using g.P_le_N) m.hy.le (hNeq ▸ g.y_upper)
    m.hbandMass.le g.mass_upper m.groupStrength_pos.le hs1 (hNeq ▸ g.E_lower)
  have hfactorEq : m.localCapFactor Ccap*Cscale=(9*Ccap*Cscale)*Real.log N := by
    unfold NativeBandModel.localCapFactor
    rw [hNeq]
    ring
  rw [hfactorEq,hNeq,hdeq,hQeq] at hb
  have hLEq : 2*Cg*Real.log N=(2*Cg)*Real.log N := rfl
  simp only [Real.rpow_zero,mul_one] at h2pow
  have hp3 : 1 ≤ N^(3*delta) := Real.one_le_rpow hN (by linarith)
  have hlast : N^(3*delta)*m.E+m.E ≤ N^(4*delta)*m.E := by
    have hh := mul_le_mul_of_nonneg_right h2pow (show 0 ≤ N^(3*delta)*m.E by have hE:=m.hE;positivity)
    have heq : N^delta*(N^(3*delta)*m.E)=N^(4*delta)*m.E := by
      rw [←mul_assoc,←Real.rpow_add hNp]
      congr 2
      ring
    rw [heq] at hh
    have hE := m.hE
    nlinarith
  change (3*F+16)*comparisonOuterPhysicalCore N delta margin gamma m.E Q C K
    ((9*Ccap*Cscale)*Real.log N) ((9*Ccap*Cscale)*Real.log N) ((2*Cg)*Real.log N) delta ≤ _ at hmain
  change (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤
    (3*F+16)*comparisonOuterPhysicalCore N delta margin gamma m.E Q C K
    ((9*Ccap*Cscale)*Real.log N) ((9*Ccap*Cscale)*Real.log N) ((2*Cg)*Real.log N) delta+
    54*m.groupStrength*(((Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*N^(-Ccut) at hb
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
