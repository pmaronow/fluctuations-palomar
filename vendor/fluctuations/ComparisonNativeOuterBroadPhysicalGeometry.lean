module

public import ComparisonNativeOuterBroadPhysicalTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 10000000

theorem native_outer_broad_diameter_eq_min
    (m : NativeBandModel) (g : NativeBroadSliceGeometry m) (cl cu : ℝ) :
    nativeOuterBroadDiameter m g cl cu =
      min m.D0 (m.localDiameter g.scale (32*cu^3/cl^3)) := by
  unfold nativeOuterBroadDiameter nativeOuterBroadTravel NativeBandModel.D0 NativeBandModel.localDiameter
  rw [mul_min_of_nonneg _ _ (show 0 ≤ 9*Real.log m.N by linarith [m.hlog])]
  congr 1
  ring

theorem native_outer_broad_diameter_physical_bounds
    (m : NativeBandModel) (g : NativeBroadSliceGeometry m)
    {cl cu Cscale J : ℝ} (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hd1 : m.d ≤ 1) (hUeq : m.U=comparisonSmallMass m.N m.E) (hU1 : m.U ≤ 1)
    (hLlower : m.N^(-(1:ℝ)) ≤ m.Lcap) (hyN : m.y ≤ m.N)
    (htravel : nativeCapTravel m ≤ m.xs) (hxv : m.xs ≤ m.bandMass)
    (hscale1 : g.scale ≤ 1) (_hCscale : 0 ≤ Cscale) (hvb : m.bandMass ≤ Cscale*g.scale)
    (hJ9 : 9 ≤ J) (hJlarge : (288*cu^3/cl^3)*Cscale ≤ J) :
    let D := nativeOuterBroadDiameter m g cl cu
    D ≤ (J*Real.log m.N)*m.bandMass ∧
    D ≤ (J*Real.log m.N)*m.N^(-m.delta)*m.E/(m.d^3*m.bandMass) ∧
    m.y/D ≤ m.N^(m.delta+2) := by
  let C := 32*cu^3/cl^3
  have hC : 0 < C := by dsimp [C]; positivity
  have hN : 0 < m.N := zero_lt_one.trans_le m.hN
  have hlog : 0 ≤ Real.log m.N := zero_le_one.trans m.hlog
  have hv : 0 < g.scale := m.hU.trans_le g.hscale
  have hD := nativeOuterBroadDiameter_pos m g hcl hcu
  have he := native_outer_broad_diameter_eq_min m g cl cu
  have hD0 : nativeOuterBroadDiameter m g cl cu ≤ m.D0 := he.trans_le (min_le_left _ _)
  have hDl : nativeOuterBroadDiameter m g cl cu ≤ m.localDiameter g.scale C :=
    he.trans_le (min_le_right _ _)
  have hglobal : nativeOuterBroadDiameter m g cl cu ≤ (J*Real.log m.N)*m.bandMass := by
    have ht := mul_le_mul_of_nonneg_left (htravel.trans hxv)
      (show 0 ≤ 9*Real.log m.N by positivity)
    have hj := mul_le_mul_of_nonneg_right hJ9 (mul_nonneg hlog m.hbandMass.le)
    change 9*Real.log m.N*nativeCapTravel m ≤ 9*Real.log m.N*m.bandMass at ht
    exact hD0.trans (ht.trans (by nlinarith only [hj]))
  have hlocal : nativeOuterBroadDiameter m g cl cu ≤
      (J*Real.log m.N)*m.N^(-m.delta)*m.E/(m.d^3*m.bandMass) := by
    apply hDl.trans
    rw [m.localDiameter_eq_physical]
    apply (div_le_div_iff₀ (mul_pos (pow_pos m.hd 3) hv)
      (mul_pos (pow_pos m.hd 3) m.hbandMass)).mpr
    have hh := mul_le_mul_of_nonneg_left hvb
      (show 0 ≤ m.localCapFactor C*m.N^(-m.delta)*m.E*m.d^3 by
        have := m.hE; have := m.hd; have := (m.localCapFactor_pos hC).le; positivity)
    have hj := mul_le_mul_of_nonneg_right hJlarge
      (show 0 ≤ Real.log m.N*m.N^(-m.delta)*m.E*m.d^3*g.scale by have := m.hE; have := m.hd; positivity)
    dsimp [NativeBandModel.localCapFactor,C] at hh ⊢
    ring_nf at hh hj ⊢
    linarith only [hh,hj]
  have hfactor : m.d^3*g.scale ≤ m.localCapFactor C := by
    have hd3 : m.d^3 ≤ 1 := pow_le_one₀ m.hd.le hd1
    have hdc : m.d^3*g.scale ≤ 1 := (mul_le_mul_of_nonneg_right hd3 hv.le).trans (by simpa using hscale1)
    have hc3 := pow_le_pow_left₀ hcl.le hclcu 3
    have hC32 : 32 ≤ C := (le_div_iff₀ (pow_pos hcl 3)).mpr (by nlinarith)
    have hh := mul_le_mul m.hlog hC32 (by norm_num : (0:ℝ) ≤ 32) hlog
    unfold NativeBandModel.localCapFactor
    nlinarith
  have hr0 := comparison_physical_reverse_ratio (delta:=m.delta) m.hN m.hlog m.hU hU1 hLlower m.hy.le hyN
  have hrl := comparison_local_diameter_reverse_ratio (delta:=m.delta) m.hN m.hd m.hE hv
    (hUeq ▸ hU1) hfactor m.hy.le hyN
  rw [←m.localDiameter_eq_physical] at hrl
  have hlow0 : m.y ≤ m.N^(m.delta+2)*m.D0 := (div_le_iff₀ m.D0_pos).mp hr0
  have hlowl : m.y ≤ m.N^(m.delta+2)*m.localDiameter g.scale C :=
    (div_le_iff₀ (m.localDiameter_pos hv hC)).mp hrl
  refine ⟨hglobal,hlocal,?_⟩
  apply (div_le_iff₀ hD).mpr
  rw [he,mul_min_of_nonneg _ _ (Real.rpow_pos_of_pos hN _).le]
  exact le_min hlow0 hlowl

theorem native_outer_broad_remainder_le_core
    (m : NativeBandModel) {width C K G J L margin gamma eps D : ℝ}
    (_hw : 0 ≤ width) (hwb : width ≤ m.bandMass)
    (hUeq : m.U=comparisonSmallMass m.N m.E) (hvU : m.U ≤ m.bandMass)
    (hgamma : 0 < gamma) (hlower : gamma*m.N^(-(2:ℝ)/3+margin)*m.d ≤ m.E)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hyv : m.y ≤ C*m.bandMass)
    (hstrength : m.N*m.groupStrength ≤ K*m.P)
    (hL : 0 ≤ L) (hsv : m.groupStrength*m.bandMass ≤ m.d^3*L)
    (hD : 0 < D) (hG : 0 ≤ G) (hJ : 0 ≤ J)
    (hglobal : D ≤ G*m.bandMass) (hlocal : D ≤ J*m.N^(-m.delta)*m.E/(m.d^3*m.bandMass))
    (hratio : m.y/D ≤ m.N^(m.delta+2)) (horder : (m.delta+2)/((m.l:ℝ)-1) ≤ eps) :
    m.groupStrength*width*(D^2+m.reverse D) ≤
      comparisonOuterPhysicalCore m.N m.delta margin gamma m.E m.Q C K G J L eps := by
  have hc := comparison_outer_ledger_physical_cost m.hl m.hN hgamma m.hE m.hd hlower
    m.P_pos m.groupStrength_pos (hUeq ▸ hvU) m.hy hC hK m.hQ hyv hstrength
    hL hsv hD hG hJ hglobal hlocal hratio horder
  change m.groupStrength*m.bandMass*(2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
    3/(m.P*m.bandMass^2)+D^2+m.reverse D) ≤ _ at hc
  have hrest := m.reverse_nonneg hD.le
  have hpositive : 0 ≤ 2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
      3/(m.P*m.bandMass^2) := by have := m.P_pos; have := m.hy; positivity
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwb m.groupStrength_pos.le) (add_nonneg (sq_nonneg D) hrest)
  have hdrop := mul_nonneg (mul_pos m.groupStrength_pos m.hbandMass).le hpositive
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
