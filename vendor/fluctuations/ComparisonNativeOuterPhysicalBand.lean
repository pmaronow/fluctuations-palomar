module

public import ComparisonNativeMasterLocalFullBand
public import ComparisonNativeLocalOrdinaryError
public import ComparisonLocalCapPhysicalSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

namespace NativeBandModel

def localCapFactor (m : NativeBandModel) (C : ℝ) : ℝ := 9*Real.log m.N*C

theorem localCapFactor_pos (m : NativeBandModel) {C : ℝ} (hC : 0 < C) :
    0 < m.localCapFactor C := by
  have hlog : 0 < Real.log m.N := by linarith [m.hlog]
  unfold localCapFactor
  positivity

theorem localDiameter_eq_physical (m : NativeBandModel) (v C : ℝ) :
    m.localDiameter v C=m.localCapFactor C*m.N^(-m.delta)*m.E/(m.d^3*v) := by
  unfold localDiameter localCapFactor
  rw [Real.rpow_neg (zero_le_one.trans m.hN)]
  ring

theorem groupStrength_mass_budget (m : NativeBandModel) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hv : m.bandMass ≤ Cg*m.ag) :
    m.groupStrength*m.bandMass ≤ m.d^3*(2*Cg*Real.log m.N) := by
  have hh := mul_le_mul_of_nonneg_left hv m.groupStrength_pos.le
  have hr := laplaceComparisonStrength_radius_upper m.hN m.hlog m.hd m.hnd m.hlam m.hld
    ⟨m.hag.le,m.hagz.trans m.hzg⟩
  have hb := mul_le_mul_of_nonneg_left hr hCg
  change m.groupStrength*m.ag ≤ 2*m.d^3*Real.log m.N at hr
  nlinarith

end NativeBandModel

theorem actual_native_outer_ordinary_error_bound
    (m : NativeBandModel) {cut q Ccap Cscale C Cg K margin gamma eps : ℝ}
    (hcut : 0 < cut) (hleft : m.cutRadius ≤ m.ag)
    (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside) (hraw : NativeBandRawMaster m)
    (hq : 0 < q) (hCcap : 0 < Ccap) (hCscale : 0 ≤ Cscale)
    (hleftMass : q ≤ m.lo+m.U) (hspan : m.hi-m.lo ≤ Ccap*q)
    (hscaleLower : q ≤ Cscale*m.bandMass) (hscaleUpper : m.bandMass ≤ Cscale*q)
    (hUeq : m.U=comparisonSmallMass m.N m.E) (hU1 : m.U ≤ 1)
    (hvU : m.U ≤ m.bandMass) (hgamma : 0 < gamma)
    (hlower : gamma*m.N^(-(2:ℝ)/3+margin)*m.d ≤ m.E)
    (hroom : m.E ≤ m.N^m.delta*m.d^3*q^2)
    (hfactor : m.d^3*q ≤ m.localCapFactor Ccap)
    (hC : 0 ≤ C) (hyv : m.y ≤ C*m.bandMass) (hyN : m.y ≤ m.N)
    (hCg : 0 ≤ Cg) (hgeom : m.bandMass ≤ Cg*m.ag)
    (hK : 0 ≤ K) (hstrength : m.N*m.groupStrength ≤ K*m.P)
    (horder : (m.delta+2)/((m.l:ℝ)-1) ≤ eps) :
    (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤
      (3*nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho+16)*
        comparisonOuterPhysicalCore m.N m.delta margin gamma m.E m.Q C K
          (m.localCapFactor Ccap*Cscale) (m.localCapFactor Ccap*Cscale)
          (2*Cg*Real.log m.N) eps+
      54*m.groupStrength*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
  have hNp : 0 < m.N := zero_lt_one.trans_le m.hN
  have hJ := m.localCapFactor_pos hCcap
  have hD := m.localDiameter_pos hq hCcap
  have hglobal : m.localDiameter q Ccap ≤ (m.localCapFactor Ccap*Cscale)*m.bandMass := by
    rw [m.localDiameter_eq_physical]
    exact (comparison_local_diameter_spatial_bound hNp m.hd hq hJ.le hroom).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscaleLower hJ.le)
  have hlocal : m.localDiameter q Ccap ≤
      (m.localCapFactor Ccap*Cscale)*m.N^(-m.delta)*m.E/(m.d^3*m.bandMass) := by
    rw [m.localDiameter_eq_physical]
    apply (div_le_div_iff₀ (mul_pos (pow_pos m.hd 3) hq)
      (mul_pos (pow_pos m.hd 3) m.hbandMass)).mpr
    have hh := mul_le_mul_of_nonneg_left hscaleUpper
      (show 0 ≤ m.localCapFactor Ccap*m.N^(-m.delta)*m.E*m.d^3 by
        have hE:=m.hE;have hd:=m.hd;positivity)
    nlinarith
  have hratio := comparison_local_diameter_reverse_ratio (delta:=m.delta) m.hN m.hd m.hE hq
    (hUeq ▸ hU1) hfactor m.hy.le hyN
  rw [←m.localDiameter_eq_physical] at hratio
  have hL : 0 ≤ 2*Cg*Real.log m.N := by have hh:=m.hlog;positivity
  have hscalar := comparison_outer_ledger_physical_cost m.hl m.hN hgamma m.hE m.hd hlower
    m.P_pos m.groupStrength_pos (hUeq ▸ hvU) m.hy hC hK m.hQ hyv hstrength hL
    (m.groupStrength_mass_budget hCg hgeom) hD (mul_nonneg hJ.le hCscale)
    (mul_nonneg hJ.le hCscale) hglobal hlocal hratio horder
  change m.groupStrength*m.bandMass*(2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
    3/(m.P*m.bandMass^2)+(m.localDiameter q Ccap)^2+m.reverse (m.localDiameter q Ccap)) ≤ _ at hscalar
  have hb := actual_master_full_ordinary_local_band_explicit m hcut hleft hupper hband hlog hraw
    hq hCcap hleftMass hspan
  have hw := native_actual_ordinary_weighted_thermal_le m
  have he := actual_native_ordinary_error_le_local_thermal m
    (fun r hr=>m.ordinary_cap_length_le_localDiameter hq hCcap hleftMass hspan hr) hband
  have hF : 0 ≤ nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho := by
    unfold nativeBinScaleLoss
    have hL := m.hLside;have hAS:=m.AS_nonneg;have hAC:=m.AC_nonneg
    have hv:=m.hbandMass;have hr:=m.rho_pos
    positivity
  have h1 := mul_le_mul_of_nonneg_left hb m.groupStrength_pos.le
  have h2 := mul_le_mul_of_nonneg_left hscalar hF
  have hDcost : m.groupStrength*m.bandMass*(m.localDiameter q Ccap)^2 ≤
      comparisonOuterPhysicalCore m.N m.delta margin gamma m.E m.Q C K
        (m.localCapFactor Ccap*Cscale) (m.localCapFactor Ccap*Cscale) (2*Cg*Real.log m.N) eps := by
    have ho : 0 ≤ 2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
        3/(m.P*m.bandMass^2)+m.reverse (m.localDiameter q Ccap) := by
      have hP:=m.P_pos;have hv:=m.hbandMass;have hy:=m.hy
      have hr:=m.reverse_nonneg hD.le
      positivity
    have hh := mul_nonneg (mul_pos m.groupStrength_pos m.hbandMass).le ho
    nlinarith
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
