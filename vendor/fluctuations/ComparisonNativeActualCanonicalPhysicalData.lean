module

public import ComparisonNativeOrdinaryPhysicalRates
public import ComparisonNativeGeneralMinimumMassGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem CommonBandGeometry.canonical_physical_data
    {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock} {p : a.Potential}
    (g : a.CommonBandGeometry p) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (ell : ℕ) (hell : 2 < ell) (Q Ccut : ℝ) (hQ : 1 ≤ Q) (hCcut : 0 ≤ Ccut)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (hd1 : a.context.d ≤ 1) (hE1 : a.context.E ≤ 1) (hElo : 1/a.context.N ≤ a.context.E)
    (hy : a.xs+1 ≤ a.context.N) :
    NativeOrdinaryPhysicalData
      ((g.canonical v hv hv1 ell hell Q (Ccut*Real.log a.context.N) hQ
        (mul_nonneg hCcut (zero_le_one.trans hlog))).toModel dphys e hlog hnd)
      Ccut 32 64 16 := by
  let b := (g.canonical v hv hv1 ell hell Q (Ccut*Real.log a.context.N) hQ
    (mul_nonneg hCcut (zero_le_one.trans hlog))).toModel dphys e hlog hnd
  have hf := g.canonical_model_facts v hv hv1 ell hell Q (Ccut*Real.log a.context.N) hQ
    (mul_nonneg hCcut (zero_le_one.trans hlog)) dphys e hlog hnd
  have hU1 : a.context.U ≤ 1 := by
    have hh := (div_le_iff₀ a.context.hN).mp hElo
    unfold NativeOverlapContext.U comparisonSmallMass
    exact (div_le_one (mul_pos a.context.hN a.context.hE)).mpr (by nlinarith)
  refine ⟨?_,hd1,hE1,hElo,rfl,hU1,hf.1,hf.2.1,hf.2.2.1,rfl,
    hf.2.2.2.2.1.le,le_rfl,?_,?_⟩
  · change (n:ℝ)+1=(n+1:ℕ)
    push_cast
    rfl
  · change 16*v ≤ 16
    linarith
  · change a.xs+min (16*v) 1 ≤ a.context.N
    linarith [min_le_right (16*v) 1]

theorem CommonBandGeometry.canonical_inner_physical_geometry
    {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock} {p : a.Potential}
    (g : a.CommonBandGeometry p) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (ell : ℕ) (hell : 2 < ell) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    {Cv Cx K : ℝ} (hdelta : 0 ≤ delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (_hCv : 0 ≤ Cv) (hCx : 0 ≤ Cx)
    (hxs : a.xs ≤ Cx*comparisonConditionalScale a.context.N delta a.context.E a.lam)
    (hvA : v ≤ Cv*comparisonConditionalScale a.context.N delta a.context.E a.lam)
    (hK : 1 ≤ K) (hKlarge : Az*Cx+16*Cv/cl ≤ K) :
    let b := (g.canonical v hv hv1 ell hell Q Lside hQ hLside).toModel dphys e hlog hnd
    b.bandMass ≤ (Cx+16*Cv)*comparisonConditionalScale b.N b.delta b.E b.lam ∧
    b.y ≤ (Cx+16*Cv)*comparisonConditionalScale b.N b.delta b.E b.lam ∧
    b.N*(b.N^(-b.delta)*b.lam) ≤ K*b.P := by
  let A := comparisonConditionalScale a.context.N delta a.context.E a.lam
  have hA : 0 < A := comparison_conditional_scale_pos a.context.hN a.context.hE a.hlam
  have hmin : min (16*v) 1 ∈ Icc (0:ℝ) 1 :=
    ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hr := a.R_le_regular_envelope hcl hAz hmin
  have hrA : a.R (min (16*v) 1) ≤ K*A := by
    have hx := mul_le_mul_of_nonneg_left hxs hAz
    have hm := div_le_div_of_nonneg_right
      ((min_le_left (16*v) 1).trans (mul_le_mul_of_nonneg_left hvA (by norm_num))) hcl.le
    have hk := mul_le_mul_of_nonneg_right hKlarge hA.le
    calc
      _ ≤ Az*a.xs+min (16*v) 1/cl := hr
      _ ≤ Az*(Cx*A)+16*(Cv*A)/cl := add_le_add hx hm
      _ = (Az*Cx+16*Cv/cl)*A := by ring
      _ ≤ K*A := hk
  have hs := comparison_canonical_inner_strength (by exact_mod_cast Nat.succ_pos n)
    hdelta a.context.hE a.context.hd a.hlam a.hld a.hupper hK
    (a.R_positive ⟨lt_min (by positivity) zero_lt_one,min_le_right _ _⟩) hrA
  have hf := g.canonical_model_facts v hv hv1 ell hell Q Lside hQ hLside dphys e hlog hnd
  dsimp only
  refine ⟨?_,?_,?_⟩
  · change 16*v ≤ (Cx+16*Cv)*A
    nlinarith [mul_nonneg hCx hA.le]
  · change a.xs+min (16*v) 1 ≤ (Cx+16*Cv)*A
    nlinarith [min_le_left (16*v) 1]
  · rw [hf.2.2.2.2.2]
    exact hs

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
