module

public import ComparisonNativeActualCanonicalPhysicalData
public import ComparisonNativeActualConditionalScales
public import ComparisonNativeActualMinimumBandRaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

namespace NativeOverlapMinimum

theorem eventually_actual_canonical_ordinary_error
    (ell : ℕ) (hell : 2 < ell+1)
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (horder : (delta+2)/(ell:ℝ) ≤ delta) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.xs=comparisonConditionalScale a.context.N delta a.context.E a.lam →
      a.xs+1 ≤ a.context.N →
      ∀p : a.Potential, ∀g : a.CommonBandGeometry p,
      ∀(v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1), a.context.U ≤ v →
      ∀(dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)),
      ∀(hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d),
      let b := (g.canonical v hv hv1 (ell+1) hell Q
        (10*Real.log a.context.N) hQ (by positivity)).toModel dphys e hlog hnd
      (∫u in 0..1,b.ordinaryMask (b.R u)*b.comparisonErrorDensity u) ≤
        a.context.N^(7*delta)*a.context.E := by
  let Cv : ℝ := max 1 (4*cu*Az)
  let Ki : ℝ := max 1 (Az+16*Cv/cl)
  have hCv1 : 1 ≤ Cv := le_max_left _ _
  have hCv0 : 0 ≤ Cv := zero_le_one.trans hCv1
  have hKi : 1 ≤ Ki := le_max_left _ _
  have hCi : 0 ≤ 1+16*Cv := by positivity
  let gamma := 1/C0
  have hgamma : 0 < gamma := one_div_pos.mpr hC0
  obtain ⟨Q,hQ,hraw⟩ := eventually_actual_minimum_canonical_band_raw ell hell Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hsR : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi := hsR.eventually (actual_native_inner_ordinary_error_eventually
    (Q:=Q) (C:=1+16*Cv) (K:=Ki) (Ccut:=10) (Ko:=32) (R:=64) (V0:=16)
    hdelta hCi hKi (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have ho := hsR.eventually (actual_native_outer_ordinary_error_eventually
    (Q:=Q) (C:=2) (K:=32*cu/cl) (Ccap:=32) (Cscale:=32) (Cg:=32*cu)
    (Ccut:=10) (Ko:=32) (R:=64) (V0:=16)
    hdelta hm.le hgamma (by norm_num) (by positivity) (by norm_num)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hraw,hi,ho,eventually_actual_minimum_physical_scalar_data hm hC0]
    with n hnraw hni hno hnscalar
  intro a hd1 hxs hy p g v hv hv1 hUv dphys e hlog hnd
  let Lside := 10*Real.log a.context.N
  have hLside : 0 ≤ Lside := by dsimp [Lside]; positivity
  let b := (g.canonical v hv hv1 (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd
  change (∫u in 0..1,b.ordinaryMask (b.R u)*b.comparisonErrorDensity u) ≤ _
  have hscalar := hnscalar a hd1
  have hdata := g.canonical_physical_data v hv hv1 (ell+1) hell Q 10 hQ (by norm_num)
    dphys e hlog hnd hd1 hscalar.1 hscalar.2.1 hy
  have hrawb := hnraw a p g v hv hv1 Lside hLside dphys e hlog hnd
  have horderb : (b.delta+2)/((b.l:ℝ)-1) ≤ delta := by
    change (delta+2)/((ell+1:ℕ)-1:ℝ) ≤ delta
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using horder
  have hbU : b.U ≤ b.bandMass := by change a.context.U ≤ 16*v; linarith
  by_cases hvA : v ≤ Cv*comparisonConditionalScale a.context.N delta a.context.E a.lam
  · have hgeom := g.canonical_inner_physical_geometry v hv hv1 (ell+1) hell Q Lside hQ hLside
      dphys e hlog hnd hdelta.le hcl hAz hCv0 (show (0:ℝ) ≤ 1 by norm_num)
      (by simpa only [one_mul] using hxs.le) hvA hKi (by simpa only [mul_one] using le_max_right (1:ℝ) (Az+16*Cv/cl))
    exact hni b rfl rfl rfl hdata hrawb hscalar.2.2.2.2.2.2.1
      hscalar.2.2.2.2.2.2.2.1 (hxs ▸ hscalar.2.2.2.2.2.1) hbU
      hgeom.1 hgeom.2.1 hgeom.2.2 horderb
  · have hvxs : a.xs ≤ v := by
      have hmul := mul_le_mul_of_nonneg_right hCv1 a.hxs.le
      rw [←hxs] at hvA
      nlinarith
    have houter : 4*cu*Az*a.xs ≤ v := by
      have hmul := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (4*cu*Az)) a.hxs.le
      rw [←hxs] at hvA
      nlinarith
    have hgeom := g.canonical_outer_physical_geometry v hv hv1 (ell+1) hell Q Lside hQ hLside
      dphys e hlog hnd hcl hcu hAz houter hvxs
    have hloc := g.canonical_local_scales v hv hv1 (ell+1) hell Q Lside hQ hLside
      dphys e hlog hnd hUv
    let q := b.lo+b.U
    have hqA : a.xs/2 ≤ q := by change a.xs/2 ≤ v/2+a.context.U; linarith [a.context.hU]
    have hroomA := comparison_conditional_outer_room (show 1 ≤ a.context.N by exact_mod_cast Nat.succ_pos n)
      hdelta.le a.context.hE a.context.hd a.hlam a.hld hscalar.2.2.2.2.2.2.2.2
    have hroomq : b.E ≤ b.N^b.delta*b.d^3*q^2 := by
      have hh : (a.xs/2)^2 ≤ q^2 := (sq_le_sq₀ (div_nonneg a.hxs.le (by norm_num)) hloc.1.le).mpr hqA
      rw [←hxs] at hroomA
      exact hroomA.trans (mul_le_mul_of_nonneg_left hh (by have hd:=a.context.hd; have hN:=a.context.hN; positivity))
    have hfactor : b.d^3*q ≤ b.localCapFactor 32 := by
      have hqbound : q ≤ 2 := by change v/2+a.context.U ≤ 2; linarith [hscalar.2.2.2.2.1]
      have hd3 : b.d^3 ≤ 1 := by exact pow_le_one₀ a.context.hd.le hd1
      have hh := mul_le_mul_of_nonneg_right hd3 hloc.1.le
      change b.d^3*q ≤ 9*Real.log a.context.N*32
      nlinarith
    have hlower : gamma*b.N^(-(2:ℝ)/3+margin)*b.d ≤ b.E := by
      change gamma*a.context.N^(-(2:ℝ)/3+margin)*a.context.d ≤ a.context.E
      have hh := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
      simpa only [gamma,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
    have hout := hno b q rfl rfl rfl hdata hrawb hloc.1 le_rfl hloc.2.1 hloc.2.2.1
      hloc.2.2.2.1 hbU hlower hroomq hfactor hgeom.2.1 hgeom.1 hgeom.2.2 horderb
    apply hout.trans
    apply mul_le_mul_of_nonneg_right _ a.context.hE.le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
