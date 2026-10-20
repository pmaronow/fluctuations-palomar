module

public import ComparisonActualHighOnlyCavityConcentrationRadius
public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

def highOnlyRadiusCutLeft (a z s gap : ℝ) : ℝ:=max a (min z (s-gap))
def highOnlyRadiusCutRight (a z s : ℝ) : ℝ:=max a (min z s)

theorem high_only_radius_single_cut_geometry {a z s gap : ℝ}
    (haz : a ≤ z) (hgap : 0 < gap) :
    a ≤ highOnlyRadiusCutLeft a z s gap ∧
    highOnlyRadiusCutLeft a z s gap ≤ highOnlyRadiusCutRight a z s ∧
    highOnlyRadiusCutRight a z s ≤ z ∧
    highOnlyRadiusCutRight a z s-highOnlyRadiusCutLeft a z s gap ≤ gap ∧
    (highOnlyRadiusCutLeft a z s gap < s ∨ s ≤ a) ∧
    (z < s ∨ s ≤ highOnlyRadiusCutRight a z s) := by
  have hleft : a ≤ highOnlyRadiusCutLeft a z s gap:=le_max_left _ _
  have horder : highOnlyRadiusCutLeft a z s gap ≤ highOnlyRadiusCutRight a z s :=
    max_le_max_left a (min_le_min_left z (sub_le_self s hgap.le))
  have hright : highOnlyRadiusCutRight a z s ≤ z:=max_le haz (min_le_left _ _)
  refine ⟨hleft,horder,hright,?_,?_,?_⟩
  · unfold highOnlyRadiusCutLeft highOnlyRadiusCutRight
    by_cases hsa : s ≤ a
    · rw [max_eq_left ((min_le_right _ _).trans hsa),
        max_eq_left ((min_le_right _ _).trans ((sub_le_self s hgap.le).trans hsa))]
      simpa only [sub_self] using hgap.le
    · by_cases hsz : z ≤ s-gap
      · rw [min_eq_left hsz,min_eq_left (hsz.trans (sub_le_self s hgap.le)),max_eq_right haz]
        simpa only [sub_self] using hgap.le
      · rw [min_eq_right (le_of_not_ge hsz)]
        by_cases has : a ≤ s-gap
        · rw [max_eq_right has]
          have H : max a (min z s) ≤ s := max_le (le_of_not_ge hsa) (min_le_right _ _)
          linarith only [H]
        · rw [max_eq_left (le_of_not_ge has)]
          have H : max a (min z s) ≤ s := max_le (le_of_not_ge hsa) (min_le_right _ _)
          linarith only [H,not_le.mp has]
  · by_cases hsa : s ≤ a
    · exact Or.inr hsa
    · left
      exact max_lt (lt_of_not_ge hsa) ((min_le_right _ _).trans_lt (sub_lt_self s hgap))
  · by_cases hsz : z < s
    · exact Or.inl hsz
    · right
      unfold highOnlyRadiusCutRight
      rw [min_eq_right (le_of_not_gt hsz)]
      exact le_max_right a s

theorem NativePullbackClockRegularity.exists_single_cut_high_only
    {alpha b h : ℝ→ℝ} {a z : ℝ}
    (H : NativePullbackClockRegularity alpha b h a z) :
    ∃s : ℝ,∀l r,a ≤ l → l ≤ r → r ≤ z → (r < s ∨ s ≤ l) →
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun t=>b (alpha t)) (Icc l r) ∧
        LipschitzOnWith Kh (fun t=>h (alpha t)) (Icc l r) := by
  rcases H with ⟨Kb,Kh,hb,hh⟩|⟨s,hs⟩
  · exact ⟨a,fun l r hal _ hrz _=>⟨Kb,Kh,
      hb.mono (Icc_subset_Icc hal hrz),hh.mono (Icc_subset_Icc hal hrz)⟩⟩
  · exact ⟨s,hs⟩

theorem high_only_radius_integral_single_cut_upper {f : ℝ→ℝ} {a l r z : ℝ}
    (hal : a ≤ l) (hlr : l ≤ r) (hrz : r ≤ z)
    (hi : IntegrableOn f (Icc a z)) (hbound : ∀t∈Icc a z,f t ≤ 1) :
    (∫t in Ioo a z,f t) ≤ (∫t in Ioo a l,f t)+(∫t in Ioo r z,f t)+(r-l) := by
  have haz : a ≤ z:=hal.trans (hlr.trans hrz)
  have hial : IntervalIntegrable f volume a l :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hal).mpr
      (hi.mono_set (Icc_subset_Icc le_rfl (hlr.trans hrz)))
  have hilr : IntervalIntegrable f volume l r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mpr
      (hi.mono_set (Icc_subset_Icc hal hrz))
  have hirz : IntervalIntegrable f volume r z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrz).mpr
      (hi.mono_set (Icc_subset_Icc (hal.trans hlr) le_rfl))
  have Hmiddle:=intervalIntegral.integral_mono_on hlr hilr
    (intervalIntegrable_const (c:=(1:ℝ))) (fun t ht=>hbound t ⟨hal.trans ht.1,ht.2.trans hrz⟩)
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at Hmiddle
  have Heq : (∫t in a..z,f t)=(∫t in a..l,f t)+(∫t in l..r,f t)+(∫t in r..z,f t) := by
    rw [←intervalIntegral.integral_add_adjacent_intervals (hial.trans hilr) hirz,
      ←intervalIntegral.integral_add_adjacent_intervals hial hilr]
  have Hconv {p q : ℝ} (hpq : p ≤ q) :
      (∫t in Ioo p q,f t)=(∫t in p..q,f t) := by
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hpq]
  rw [Hconv haz,Hconv hal,Hconv hrz,Heq]
  linarith only [Hmiddle]

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def cavityRadiusPointDefect (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) : ℝ :=
  orderedPathB (n+1) M.bf M.hf (M.alpha.val.val r)-
    (orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r))^2

theorem cavityRadiusPointDefect_nonneg
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) : 0≤M.cavityRadiusPointDefect r := by
  have H:=M.radius_moments
  exact sub_nonneg.mpr ((H.2.2 r hr).2.1)

theorem cavityRadiusPointDefect_integrableOn
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a z : ℝ} (ha : 0≤a) (hz : z≤1) :
    IntegrableOn M.cavityRadiusPointDefect (Ioo a z) := by
  have H:=M.radius_moments
  have hS2 : MonotoneOn (fun r=>(orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r))^2)
      (Icc (0:ℝ) 1) := by
    intro r hr s hs hrs
    exact pow_le_pow_left₀ ((H.2.2 r hr).1.1) (H.1 hr hs hrs) 2
  have hiB:=H.2.1.integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hiS:=hS2.integrableOn_isCompact (μ:=volume) isCompact_Icc
  exact (hiB.sub hiS).mono_set (fun r hr=>⟨ha.trans hr.1.le,hr.2.le.trans hz⟩)

theorem cavityRadiusDefect_eq_point_integral
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (a z : ℝ) :
    M.cavityRadiusDefect a z=∫r in Ioo a z,M.cavityRadiusPointDefect r := rfl

theorem cavityRadiusPointDefect_le_one
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) : M.cavityRadiusPointDefect r ≤ 1 := by
  have HB:=(M.radius_moments.2.2 r hr).2.2
  dsimp only [radiusB] at HB
  unfold cavityRadiusPointDefect
  nlinarith only [HB,sq_nonneg (orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r))]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
