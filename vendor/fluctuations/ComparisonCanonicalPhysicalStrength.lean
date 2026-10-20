module

public import ComparisonNativeCanonicalBandGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7200000

theorem comparison_conditional_scale_strength_product {N delta E d lam : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hd : 0 < d) (hlam : 0 < lam)
    (hld : lam ≤ d^2) (hupper : Real.sqrt N*E ≤ d^2) :
    lam*comparisonConditionalScale N delta E lam ≤ N^delta*d^3 := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hs2 := Real.sq_sqrt hlam.le
  have hslo : Real.sqrt lam ≤ d := by nlinarith [Real.sqrt_nonneg lam]
  have hh := mul_le_mul hupper hslo hs.le (sq_nonneg d)
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hN delta).le
  have he : lam*comparisonConditionalScale N delta E lam=
      N^delta*(Real.sqrt N*E)*Real.sqrt lam := by
    unfold comparisonConditionalScale
    field_simp
    ring_nf
    rw [hs2]
  rw [he]
  nlinarith

theorem comparison_canonical_inner_strength {N delta E d lam K r : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta) (hE : 0 < E) (hd : 0 < d)
    (hlam : 0 < lam) (hld : lam ≤ d^2) (hupper : Real.sqrt N*E ≤ d^2)
    (hK : 1 ≤ K) (hr : 0 < r) (hrA : r ≤ K*comparisonConditionalScale N delta E lam) :
    N*(N^(-delta)*lam) ≤ K*(N*laplaceComparisonStrength d lam r) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hpow : 1 ≤ N^delta := Real.one_le_rpow hN hdelta
  have hprod := comparison_conditional_scale_strength_product (delta:=delta) hNp hE hd hlam hld hupper
  have hrprod : lam*r ≤ K*N^delta*d^3 := by
    have hh := mul_le_mul_of_nonneg_left hrA hlam.le
    have ht := mul_le_mul_of_nonneg_left hprod hKp.le
    nlinarith
  have hden : 0 < K*N^delta := mul_pos hKp (Real.rpow_pos_of_pos hNp delta)
  have hlamlo : lam/(K*N^delta) ≤ lam := by
    apply (div_le_iff₀ hden).mpr
    have hk : 1 ≤ K*N^delta := by nlinarith
    nlinarith
  have hrlo : lam/(K*N^delta) ≤ d^3/r :=
    (div_le_div_iff₀ hden hr).mpr (by nlinarith)
  have hleaf := (le_min hlamlo hrlo).trans (laplaceComparisonStrength_lower hd hlam hr)
  have hm := (div_le_iff₀ hden).mp hleaf
  have hh := mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hNp (-delta)).le
  have he : N^(-delta)*(laplaceComparisonStrength d lam r*(K*N^delta))=
      K*laplaceComparisonStrength d lam r := by
    rw [Real.rpow_neg hNp.le]
    field_simp
  rw [he] at hh
  have ht := mul_le_mul_of_nonneg_left hh hNp.le
  nlinarith

namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem R_le_regular_envelope
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    a.R u ≤ Az*a.xs+u/cl := by
  by_cases hz : a.R u ≤ a.z
  · have hh := hz.trans a.hzxs
    have hu0 : 0 ≤ u/cl := div_nonneg hu.1 hcl.le
    linarith
  · have hr := comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha u
    have hh := (a.regular (a.R u) ⟨(lt_of_not_ge hz).le,hr.2⟩).1
    rw [comparisonSweepQuantile_spec a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha hu] at hh
    have huR : a.R u ≤ u/cl := (le_div_iff₀ hcl).mpr (by nlinarith)
    have hAx : 0 ≤ Az*a.xs := mul_nonneg hAz a.hxs.le
    linarith

theorem CommonBandGeometry.canonical_outer_physical_geometry
    {a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock} {p : a.Potential}
    (g : a.CommonBandGeometry p) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (l : ℕ) (hl : 2 < l) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (houter : 4*cu*Az*a.xs ≤ v) (hxs : a.xs ≤ v) :
    let b := (g.canonical v hv hv1 l hl Q Lside hQ hLside).toModel dphys e hlog hnd
    b.bandMass ≤ (32*cu)*b.ag ∧ b.y ≤ 2*b.bandMass ∧
      b.N*b.groupStrength ≤ (32*cu/cl)*b.P := by
  let b := (g.canonical v hv hv1 l hl Q Lside hQ hLside).toModel dphys e hlog hnd
  have hr := a.canonical_outer_radii hv hv1 hcl hcu hAz houter
  have hleft : v ≤ 2*cu*b.ag := by
    change v ≤ 2*cu*a.R (v/2)
    have hh := (div_le_iff₀ (by positivity : 0 < 2*cu)).mp hr.2.1
    nlinarith
  have hright : b.zg*cl ≤ 16*v := (le_div_iff₀ hcl).mp hr.2.2
  have hf := g.canonical_model_facts v hv hv1 l hl Q Lside hQ hLside dphys e hlog hnd
  have hag01 : b.ag∈Icc (0:ℝ) 1 := ⟨b.hag.le,b.hagz.trans b.hzg⟩
  have hzg01 : b.zg∈Icc (0:ℝ) 1 := ⟨b.hag.le.trans b.hagz,b.hzg⟩
  have hmono := (laplaceComparisonStrength_monotonicities b.hd.ne' b.hlam (r₀:=0) le_rfl).2 hag01 hzg01 b.hagz
  have he : 0 < laplaceComparisonStrength b.d b.lam b.zg := laplaceComparisonStrength_pos b.d b.hlam _
  change b.groupStrength*b.ag ≤ laplaceComparisonStrength b.d b.lam b.zg*b.zg at hmono
  have hratio : b.groupStrength ≤ (32*cu/cl)*laplaceComparisonStrength b.d b.lam b.zg := by
    have hgeo : b.zg ≤ (32*cu/cl)*b.ag := by
      calc
        _ ≤ (32*cu*b.ag)/cl := (le_div_iff₀ hcl).mpr (by nlinarith)
        _ = _ := by ring
    have hh := mul_le_mul_of_nonneg_left hgeo he.le
    apply le_of_mul_le_mul_right (a:=b.ag) _ b.hag
    nlinarith
  refine ⟨?_,?_,?_⟩
  · change 16*v ≤ (32*cu)*b.ag
    nlinarith
  · change a.xs+min (16*v) 1 ≤ 2*(16*v)
    linarith [min_le_left (16*v) 1]
  · have hh := mul_le_mul_of_nonneg_left hratio (zero_le_one.trans b.hN)
    rw [hf.2.2.2.2.2]
    nlinarith

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
