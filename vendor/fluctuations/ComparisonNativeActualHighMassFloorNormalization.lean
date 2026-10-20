module

public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_high_floor_slab_normalized_le {x W v hi U N delta cu c K : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) (hcu : 0 < cu) (hc : 0 < c)
    (hhi : 0 ≤ hi) (hhi2 : hi ≤ 2*v) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hxW : x ≤ W) (hvlo : c*W ≤ v) :
    (K*(x+hi)^2*N^delta*U^2/(v/cu))/(x^4*v/W^2) ≤
      (K*cu*(1/c+2)^2)*N^delta*(U^2*W^2/x^4) := by
  have hxv : x ≤ v/c := by
    apply hxW.trans
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
  have hs : x+hi ≤ (1/c+2)*v := by
    calc
      _ ≤ v/c+2*v := add_le_add hxv hhi2
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ (add_nonneg hx.le hhi) hs 2
  have hm := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ K*N^delta*U^2*cu*W^2/(x^4*v^2) by positivity)
  have he₁ : (K*N^delta*U^2*cu*W^2/(x^4*v^2))*(x+hi)^2=
      (K*(x+hi)^2*N^delta*U^2/(v/cu))/(x^4*v/W^2) := by field_simp
  have he₂ : (K*N^delta*U^2*cu*W^2/(x^4*v^2))*((1/c+2)*v)^2=
      (K*cu*(1/c+2)^2)*N^delta*(U^2*W^2/x^4) := by field_simp
  rw [he₁,he₂] at hm
  exact hm

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_direct_test_floor_strong_rate
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs) :
    a.context.N^delta*(a.context.U^2*a.canonicalDirectTestBandScale^2/a.xs^4) ≤
      (Cs+1)^2*C0^6*a.context.N^(-(6*m-delta)) := by
  have hE := a.context.hE
  have hd := a.context.hd
  have hN := a.context.hN
  have hx := a.hxs
  have HW := a.canonical_direct_test_band_pos
  have Hcap := a.canonical_direct_test_cap_strong_rate hC0 hCs hsmall
  have Hcritical := a.canonical_high_mass_critical_ratio hC0
  have Hcap0 : 0 ≤ (a.context.E/a.context.d^3)*(a.canonicalDirectTestBandScale^2/a.xs^4) := by positivity
  have Hcritical0 : 0 ≤ a.context.d^3/(a.context.N^2*a.context.E^3) := by positivity
  have Hmul := mul_le_mul Hcap Hcritical Hcritical0
    (show 0 ≤ (Cs+1)^2*C0^3*a.context.N^(-3*m) by positivity)
  have he : ((a.context.E/a.context.d^3)*(a.canonicalDirectTestBandScale^2/a.xs^4))*
      (a.context.d^3/(a.context.N^2*a.context.E^3))=
      a.context.U^2*a.canonicalDirectTestBandScale^2/a.xs^4 := by
    unfold NativeOverlapContext.U comparisonSmallMass
    field_simp
  rw [he] at Hmul
  have Hfinal := mul_le_mul_of_nonneg_left Hmul (Real.rpow_nonneg hN.le delta)
  have he₂ : a.context.N^delta*((Cs+1)^2*C0^3*a.context.N^(-3*m)*
      (C0^3*a.context.N^(-3*m)))=(Cs+1)^2*C0^6*a.context.N^(-(6*m-delta)) := by
    calc
      _ = (Cs+1)^2*C0^6*((a.context.N^delta*a.context.N^(-3*m))*a.context.N^(-3*m)) := by ring
      _ = (Cs+1)^2*C0^6*a.context.N^(delta+-3*m+-3*m) := by
        rw [←Real.rpow_add hN,←Real.rpow_add hN]
      _ = _ := by rw [show delta+-3*m+-3*m=-(6*m-delta) by ring]
  rw [he₂] at Hfinal
  exact Hfinal

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
