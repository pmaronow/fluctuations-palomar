module

public import SKProof.Port.ComparisonActualOriginalQVirtualContactData
public import SKProof.Port.ComparisonActualOriginalQLargerWorkingScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem actual_virtual_contact_eventually_along
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (p : (n:ℕ)→(M n).Potential)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    {t c eta : ℝ} (hsupport : t∈comparisonIncrementSupport V)
    (ht : 0 ≤ t) (hc : 0 < c) (heta : 0 < eta)
    (hRight : ∀eps,0 < eps→eps ≤ eta→c < V (t+eps)) :
    ∀eps>0,∀ᶠn in atTop,∃z∈Ioc (0:ℝ) 1,
      |z/(M n).xs-t| < eps ∧ (p n).H z=0 ∧ c*(M n).xs ≤ (M n).alpha.val.val z := by
  have hfloor := actual_floor_mass_ratio_tendsto_zero_along hC0 hroom dim hdim M
    (fun n=>(M n).xs) (fun _=>le_rfl)
  have htravel := actual_cap_travel_ratio_tendsto_zero_along hC0 hroom dim hdim M
    (fun n=>(M n).xs) (fun _=>le_rfl)
  have hcontacts := comparison_native_virtual_contact_eventually
    (fun n=>(p n).toVirtualContactData) (fun n=>(M n).xs) V hV hsupport ht hc heta hRight
    (fun n=>(M n).hxs) hxs (by simpa only [Potential.toVirtualContactData] using G.omission_over_test_zero_original_q) hCDF hfloor htravel
  intro eps heps
  have hsmall : ∀ᶠn in atTop,(M n).xs*(t+eps) < 1 := by
    have H : Tendsto (fun n=>(M n).xs*(t+eps)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const (t+eps)
    exact H.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hcontacts eps heps,hsmall,G.positive_bands_high_original_q (c/2) (half_pos hc)] with n hn hnsmall hnomit
  obtain ⟨z,hclose,hzero,hmass⟩ := hn
  change (p n).H z=0 at hzero
  change c*(M n).xs ≤ (M n).alpha.val.val z at hmass
  have hz0 : 0 < z := by
    by_contra hz
    have H := (M n).alpha.val.property.2
      ((le_of_not_gt hz).trans (M n).data.rmin_nonneg)
    rw [(M n).alpha.property.1] at H
    nlinarith [mul_pos hc (M n).hxs]
  have hz1 : z ≤ 1 := by
    have H : z/(M n).xs < t+eps := by linarith [(abs_lt.mp hclose).2]
    have H' := (div_lt_iff₀ (M n).hxs).mp H
    nlinarith only [H',hnsmall]
  exact ⟨z,⟨hz0,hz1⟩,hclose,hzero,hmass⟩

theorem actual_virtual_gap_endpoint_contacts_eventually_along
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (p : (n:ℕ)→(M n).Potential)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hasupport : a∈comparisonIncrementSupport V) (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2)) :
    let c := V ((a+b)/2)/2
    0 < c ∧ ∀eps>0,∀ᶠn in atTop,
      (∃z∈Ioc (0:ℝ) 1,|z/(M n).xs-a| < eps ∧ (p n).H z=0 ∧
        c*(M n).xs ≤ (M n).alpha.val.val z) ∧
      (∃z∈Ioc (0:ℝ) 1,|z/(M n).xs-b| < eps ∧ (p n).H z=0 ∧
        c*(M n).xs ≤ (M n).alpha.val.val z) := by
  dsimp only
  have hc : 0 < V ((a+b)/2)/2 := half_pos hmass
  have heta : 0 < (b-a)/2 := by linarith
  have hRightA : ∀eps,0 < eps→eps ≤ (b-a)/2→V ((a+b)/2)/2 < V (a+eps) := by
    intro eps heps he
    rw [comparison_increment_support_gap_constant hV hgap (a+eps)
      ⟨by linarith,by linarith⟩ ((a+b)/2) ⟨by linarith,by linarith⟩]
    linarith
  have hRightB : ∀eps,0 < eps→eps ≤ (b-a)/2→V ((a+b)/2)/2 < V (b+eps) := by
    intro eps heps _
    exact (by linarith : V ((a+b)/2)/2 < V ((a+b)/2)).trans_le (hV (by linarith))
  have hA := actual_virtual_contact_eventually_along hC0 hroom dim hdim M G p hxs V hV hCDF
    hasupport ha hc heta hRightA
  have hB := actual_virtual_contact_eventually_along hC0 hroom dim hdim M G p hxs V hV hCDF
    hbsupport (ha.trans hab.le) hc heta hRightB
  exact ⟨hc,fun eps heps=>(hA eps heps).and (hB eps heps)⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
