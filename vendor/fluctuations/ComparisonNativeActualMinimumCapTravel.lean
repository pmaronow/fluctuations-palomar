module

public import ComparisonNativeActualMinimumCapGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def cavityCapTravel
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) : ℝ :=
  (a.context.L/a.context.N^delta)*Real.log ((1+a.context.U)/a.context.U)

theorem Potential.cap_interval_travel
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1)
    (hnegative : ∀t ∈ Ioo l r, p.H t < 0) : r-l ≤ a.cavityCapTravel := by
  have hbang : ∀ᵐ t, t∈Icc (0:ℝ) 1 → p.H t < 0 →
      deriv a.alpha.val.val t = comparisonCap a.context.N delta a.context.U
        a.context.L a.context.E a.context.d (a.alpha.val.val t) := p.hbang
  exact (potential_comparison_cap_interval_travel a.context.hN a.context.hU a.context.hL
    a.context.hE a.context.hd (inverseIntegralConstraints_lipschitz a.context.hm a.context.hM a.alpha.property)
    (inverseConstraint_strictMonoOn a.context.hc a.context.hk a.context.hkc a.alpha.property)
    (fun t _ => a.alpha.val.property.1 t) hbang hl hr hlr.le hnegative).2.1

end NativeOverlapMinimum

theorem eventually_actual_minimum_cap_travel_small
    {m delta cl cu Az C0 Ct D Bclock epsilon : ℝ}
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta) (hepsilon : 0 < epsilon) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.cavityCapTravel ≤ epsilon*a.xs ∧
        ∀(p : a.Potential) (l r : ℝ), 0 ≤ l → l < r → r ≤ 1 →
          (∀t ∈ Ioo l r, p.H t < 0) → r-l ≤ epsilon*a.xs := by
  have htravel := (tendsto_add_atTop_nat 1).eventually
    (eventually_comparisonTravel_small (C:=C0) (D:=D) hC0 hroom hepsilon)
  filter_upwards [htravel] with n hn
  intro a
  have hc : a.cavityCapTravel ≤ epsilon*a.xs := by
    exact (hn a.context.E a.context.d a.context.hE a.context.hd a.hdD a.hupper a.hlower).trans
      (mul_le_mul_of_nonneg_left a.hscale hepsilon.le)
  refine ⟨hc,?_⟩
  intro p l r hl hlr hr hnegative
  exact (p.cap_interval_travel hl hlr hr hnegative).trans hc

theorem eventually_actual_minimum_inner_parent_cap_scale
    {m delta cl cu Az C0 Ct D Bclock C : ℝ}
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(p : a.Potential) (l r t : ℝ), 0 ≤ l → l < r → r ≤ 1 →
        (∀s ∈ Ioo l r, p.H s < 0) → t∈Ioo l r → t ≤ C*a.xs →
        r ≤ (C+1)*a.xs ∧
          a.xs+a.alpha.val.val r ≤ (1+cu*(C+1+Az))*a.xs := by
  filter_upwards [eventually_actual_minimum_cap_travel_small (D:=D) (epsilon:=1)
    hC0 hroom zero_lt_one] with n hn
  intro a p l r t hl hlr hr hnegative ht hinner
  have hw := (hn a).2 p l r hl hlr hr hnegative
  simp only [one_mul] at hw
  have hright : r ≤ (C+1)*a.xs := by nlinarith [ht.1,ht.2]
  have hmax : max r a.z ∈ Icc a.z 1 := ⟨le_max_right _ _, max_le hr a.hz.2⟩
  have hm : max r a.z ≤ (C+1+Az)*a.xs := by
    apply max_le
    · nlinarith [mul_nonneg hAz a.hxs.le]
    · nlinarith [a.hzxs]
  have hu := (a.alpha.val.property.2 (le_max_left r a.z)).trans (a.regular _ hmax).2
  have hu' := mul_le_mul_of_nonneg_left hm hcu.le
  refine ⟨hright,?_⟩
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
