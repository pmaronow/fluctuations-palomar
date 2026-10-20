module

public import ComparisonActualHighOnlyWeakComparableClocks
public import ComparisonActualHighOnlyClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 margin : ℝ} {dim : ℕ → ℕ}

theorem coefficient_at_omitted_cutoff {n : ℕ}
    (P : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    P.coefficient P.data.s=P.lam := by
  have HR : P.R P.data.s=0 := omittedSweepQuantile_left zero_le_one
    ⟨P.data.hs.1,P.data.hs1⟩ P.data.hc P.data.hk P.data.hkc
      P.data.hm P.data.hM P.alpha
  change omittedStrengthCoefficient P.data.d P.data.s P.R P.lam P.data.s=P.lam
  rw [omittedStrengthCoefficient,ite_eq_left (le_refl P.data.s),HR]
  simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]

theorem coefficient_below_omitted_cutoff {n : ℕ}
    (P : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u<P.data.s) : P.coefficient u=0 := by
  change omittedStrengthCoefficient P.data.d P.data.s P.R P.lam u=0
  simp only [omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu)]

inductive ActualFiniteHighOnlyMatrixHistory (c0 : ℝ)
    (root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock) :
    ℕ → ((n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock) → Prop
  | root : ActualFiniteHighOnlyMatrixHistory c0 root 0 root
  | child {q : ℕ}
      {P Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
        m delta cl cu Az C0 Ct D Bclock}
      (history : ActualFiniteHighOnlyMatrixHistory c0 root q P)
      (x : ℕ → ℝ) (hunit : ∀ᶠn in atTop,x n≤1)
      (hd : ∀ᶠn in atTop,(Q n).context.d=c0*x n)
      (hs : ∀ᶠn in atTop,(Q n).data.s=(P n).data.s)
      (hb : ∀ᶠn in atTop,∀u,(Q n).b u=(P n).b u-(P n).coefficient u) :
      ActualFiniteHighOnlyMatrixHistory c0 root (q+1) Q

theorem ActualFiniteHighOnlyMatrixHistory.same_omission
    {root M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock} {q : ℕ}
    (H : ActualFiniteHighOnlyMatrixHistory c0 root q M) :
    ∀ᶠn in atTop,(M n).data.s=(root n).data.s := by
  induction H with
  | root => exact Eventually.of_forall (fun _ => rfl)
  | child history x hunit hd hs hb ih =>
    filter_upwards [ih,hs] with n hn hns
    exact hns.trans hn

theorem ActualFiniteHighOnlyMatrixHistory.radius_cap
    (hc0 : 0≤c0)
    {root M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock} {q : ℕ}
    (H : ActualFiniteHighOnlyMatrixHistory c0 root q M)
    (hroot : ∀ᶠn in atTop,(root n).context.d≤c0) :
    ∀ᶠn in atTop,(M n).context.d≤c0 := by
  induction H with
  | root => exact hroot
  | child history x hunit hd hs hb ih =>
    filter_upwards [hunit,hd] with n hn hnd
    rw [hnd]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hc0

theorem ActualFiniteHighOnlyMatrixHistory.low_gap
    (hc0 : 0≤c0)
    {root M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock} {q : ℕ}
    (H : ActualFiniteHighOnlyMatrixHistory c0 root q M)
    (hrootCap : ∀ᶠn in atTop,(root n).context.d≤c0)
    (hrootGap : ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (root n).data.s,
      (root n).b u+margin≤(root n).b (root n).data.s) :
    ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (M n).data.s,
      (M n).b u+margin-(q:ℝ)*c0^2≤(M n).b (M n).data.s := by
  induction H with
  | root =>
    filter_upwards [hrootGap] with n hn u hu
    simpa only [Nat.cast_zero,zero_mul,sub_zero] using hn u hu
  | @child q P Q history x hunit hd hs hb ih =>
    have hcap := history.radius_cap hc0 hrootCap
    filter_upwards [ih,hcap,hs,hb] with n hgap hpcap hsame hbare
    intro u hu
    have huP : u∈Ico (0:ℝ) (P n).data.s := by simpa only [←hsame] using hu
    have hlow := (P n).coefficient_below_omitted_cutoff huP.2
    have hhigh := (P n).coefficient_at_omitted_cutoff
    have hlam : (P n).lam≤c0^2 := (P n).hld.trans
      (pow_le_pow_left₀ (P n).context.hd.le hpcap 2)
    have hcast : ((q+1:ℕ):ℝ)*c0^2=(q:ℝ)*c0^2+c0^2 := by
      push_cast
      ring
    rw [hsame,hbare u,hbare (P n).data.s,hlow,hhigh,hcast]
    nlinarith only [hgap u huP,hlam]

theorem ActualFiniteHighOnlyMatrixHistory.next_child_room
    (hc0 : 0≤c0)
    {root M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock} {q : ℕ}
    (H : ActualFiniteHighOnlyMatrixHistory c0 root q M)
    (hrootCap : ∀ᶠn in atTop,(root n).context.d≤c0)
    (hrootGap : ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (root n).data.s,
      (root n).b u+margin≤(root n).b (root n).data.s)
    (hrootPos : ∀ᶠn in atTop,0<(root n).data.s)
    (hbudget : ((q:ℝ)+2)*c0^2≤ margin)
    (x : ℕ → ℝ) (hx : ∀n,0<x n) (hunit : ∀ᶠn in atTop,x n≤1) :
    ∀ᶠn in atTop,
      (M n).lam+(c0*x n)^2≤(M n).b (M n).data.s ∧
      ∀u∈Ico (0:ℝ) (M n).data.s,
        (M n).b u+(M n).lam+(c0*x n)^2≤(M n).b (M n).data.s := by
  have hgap := H.low_gap hc0 hrootCap hrootGap
  have hcap := H.radius_cap hc0 hrootCap
  have hpos : ∀ᶠn in atTop,0<(M n).data.s := by
    filter_upwards [H.same_omission,hrootPos] with n hnS hnP
    rw [hnS]
    exact hnP
  filter_upwards [hgap,hcap,hunit,hpos] with n hnGap hnCap hnUnit hnPos
  have hlam : (M n).lam≤c0^2 := (M n).hld.trans
    (pow_le_pow_left₀ (M n).context.hd.le hnCap 2)
  have hcx : c0*x n≤c0 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnUnit hc0
  have hcx0 : 0≤c0*x n := mul_nonneg hc0 (hx n).le
  have hrad : (c0*x n)^2≤c0^2 := pow_le_pow_left₀ hcx0 hcx 2
  have hzero : (0:ℝ)∈Ico 0 (M n).data.s := ⟨le_rfl,hnPos⟩
  have hbase := hnGap 0 hzero
  have hb0 : 0≤(M n).b 0 := (M n).hb0
  constructor
  · nlinarith only [hbase,hb0,hlam,hrad,hbudget]
  · intro u hu
    nlinarith only [hnGap u hu,hlam,hrad,hbudget]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
