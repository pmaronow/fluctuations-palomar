module

public import ComparisonNativeFiniteErrorHistory
public import ComparisonNativeActualWeakSelectedHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

inductive ActualWeakNativeErrorGrowthHistory
    (c0 : ℝ)
    (root : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ℕ → ((n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) → Prop
  | root : ActualWeakNativeErrorGrowthHistory c0 root 0 root
  | child {depth : ℕ}
      {P Q : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
      (history : ActualWeakNativeErrorGrowthHistory c0 root depth P)
      (unit : ∀ᶠn in atTop,(P n).xs ≤ 1)
      (target : ∀ᶠn in atTop,comparisonConditionalScale (P n).context.N delta
        (P n).context.E (P n).lam ≤ (P n).xs)
      (weak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (P n).xs/(P n).xs^2)
        atTop (𝓝 0))
      (radius : ∀ᶠn in atTop,(Q n).context.d=c0*(P n).xs)
      (error : ∀ᶠn in atTop,(Q n).context.E=actualChildErrorBudget (dim n+1) delta c0
        (P n).context.d (P n).lam (P n).xs)
      (matrix : ∀ᶠn in atTop,∀u,(Q n).b u=(P n).b u-
        laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u))
      (field : ∀ᶠn in atTop,∀u,(Q n).h u=(P n).h u+
        laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u)
      (growth : ∀ᶠn in atTop,((dim n+1:ℕ):ℝ)^(delta/4)*(P n).context.E ≤ (Q n).context.E) :
      ActualWeakNativeErrorGrowthHistory c0 root (depth+1) Q

theorem ActualWeakNativeErrorGrowthHistory.comp
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualWeakNativeErrorGrowthHistory c0 root depth M)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualWeakNativeErrorGrowthHistory c0 (fun n=>root (phi n)) depth (fun n=>M (phi n)) := by
  induction H with
  | root => exact .root
  | child history unit target weak radius error matrix field growth ih =>
    exact .child ih (hphi.eventually unit) (hphi.eventually target) (weak.comp hphi)
      (hphi.eventually radius) (hphi.eventually error) (hphi.eventually matrix)
      (hphi.eventually field) (hphi.eventually growth)

theorem ActualWeakNativeErrorGrowthHistory.weak_history
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualWeakNativeErrorGrowthHistory c0 root depth M) :
    ActualWeakSelectedHistoryChain c0 root M := by
  induction H with
  | root => exact .root
  | @child depth P Q history unit target weak radius error matrix field growth ih =>
    exact .child ih (fun n=>(P n).xs) (fun n=>(P n).hxs) unit target
      (Eventually.of_forall fun n=>(P n).hzxs) weak radius error matrix field

theorem ActualWeakNativeErrorGrowthHistory.error_history
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualWeakNativeErrorGrowthHistory c0 root depth M) :
    ActualNativeErrorGrowthHistory root depth M := by
  induction H with
  | root => exact .root
  | child history unit target weak radius error matrix field growth ih => exact .child ih growth

theorem ActualWeakNativeErrorGrowthHistory.radius_cap
    (hc0 : 0 ≤ c0)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualWeakNativeErrorGrowthHistory c0 root depth M)
    (hroot : ∀ᶠn in atTop,(root n).context.d ≤ c0) :
    ∀ᶠn in atTop,(M n).context.d ≤ c0 := by
  induction H with
  | root => exact hroot
  | child history unit target weak radius error matrix field growth ih =>
    filter_upwards [radius,unit] with n hnR hnU
    rw [hnR]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnU hc0

theorem ActualWeakNativeErrorGrowthHistory.matrix_defect
    (hc0 : 0 ≤ c0)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualWeakNativeErrorGrowthHistory c0 root depth M)
    (hroot : ∀ᶠn in atTop,(root n).context.d ≤ c0) :
    ∀ᶠn in atTop,(root n).b 0-(M n).b 0 ≤ (depth:ℝ)*c0^2 := by
  induction H with
  | root => filter_upwards [] with n; simp only [sub_self,Nat.cast_zero,zero_mul,le_refl]
  | @child depth P Q history unit target weak radius error matrix field growth ih =>
    have HP:=history.radius_cap hc0 hroot
    filter_upwards [HP,matrix,ih] with n hnP hnM hnI
    have Hlam : (P n).lam ≤ c0^2 := (P n).hld.trans
      (pow_le_pow_left₀ (P n).context.hd.le hnP 2)
    have He:=laplaceComparisonStrength_le (P n).context.d (P n).hlam.le ((P n).R 0)
    rw [hnM 0]
    push_cast
    nlinarith only [Hlam,He,hnI]

theorem ActualWeakNativeErrorGrowthHistory.covariance_room
    (hc0 : 0 ≤ c0)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualWeakNativeErrorGrowthHistory c0 root depth M)
    (hroot : ∀ᶠn in atTop,(root n).context.d ≤ c0)
    (hbase : ∀ᶠn in atTop,T-1 ≤ (root n).b 0)
    (hunit : ∀ᶠn in atTop,(M n).xs ≤ 1)
    (hbudget : ((depth:ℝ)+2)*c0^2 ≤ T-1) :
    ∀ᶠn in atTop,(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b 0 := by
  filter_upwards [H.matrix_defect hc0 hroot,H.radius_cap hc0 hroot,hbase,hunit] with n hnDef hnD hnBase hnUnit
  have Hlam : (M n).lam ≤ c0^2 := (M n).hld.trans
    (pow_le_pow_left₀ (M n).context.hd.le hnD 2)
  have Hrad : (c0*(M n).xs)^2 ≤ c0^2 := pow_le_pow_left₀
    (mul_nonneg hc0 (M n).hxs.le) (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hnUnit hc0) 2
  nlinarith only [hnDef,hnBase,Hlam,Hrad,hbudget]

theorem ActualWeakNativeErrorGrowthHistory.false_at_propagation_depth
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hdim : Tendsto dim atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakNativeErrorGrowthHistory c0 root (actualPropagationDepth delta) M) : False :=
  H.error_history.false_at_propagation_depth hm hdelta hC0 hdim

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
