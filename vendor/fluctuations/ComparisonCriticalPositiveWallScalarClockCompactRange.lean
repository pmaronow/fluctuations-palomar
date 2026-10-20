module

public import ComparisonActualHighWallCriticalClockRadiusPointwise
public import ComparisonCriticalPositiveWallPhysicalScalarClockAlong
public import ComparisonActualHighWallStarPreparatory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

theorem eventually_critical_positive_wall_scalar_clock_compact_range
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hrmin : Tendsto (fun n=>(M n).data.rmin/(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ)
    (hCDF : ∀r,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*r)/(M n).xs)
      atTop (𝓝 (V r)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃Q : ℝ,0 < Q ∧ ∀ᶠn in atTop,∀t∈Icc a b,
      actualMixedClock (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t))/(T*(M n).xs)∈Icc (0:ℝ) Q := by
  obtain ⟨B,hB,HB⟩ := eventually_actual_high_wall_mass_mean_upper
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C := max (V b+1) 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  have Hcap : ∀ᶠn in atTop,∀t∈Icc a b,
      (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs := by
    have hvC : V b < C := by
      dsimp only [C]
      linarith [le_max_left (V b+1) 1]
    have H := (hCDF b).eventually (eventually_le_nhds hvC)
    filter_upwards [H] with n hn t ht
    have hmono := (M n).alpha.val.property.2
      (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le)
    have hcap := (div_le_iff₀ (M n).hxs).mp hn
    exact hmono.trans (by simpa only [mul_comm] using hcap)
  have Hrad : ∀ᶠn in atTop,∀t∈Icc a b,
      (M n).xs*t∈Icc (M n).data.rmin 1 := by
    have Hlow : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*a := by
      filter_upwards [hrmin.eventually (gt_mem_nhds ha)] with n hn
      simpa only [mul_comm] using (div_lt_iff₀ (M n).hxs).mp hn
    have Hhigh : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
      have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
        simpa only [zero_mul] using hx.mul_const b
      exact H.eventually (eventually_le_nhds zero_lt_one)
    filter_upwards [Hlow,Hhigh] with n hnlo hnhi t ht
    exact ⟨hnlo.le.trans (mul_le_mul_of_nonneg_left ht.1 (M n).hxs.le),
      (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hnhi⟩
  have Hsmall : ∀ᶠn in atTop,(M n).data.d^2 ≤ (M n).data.T := by
    have H : Tendsto (fun n=>(M n).data.d^2) atTop (𝓝 0) := by
      have Hd : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0) := by
        simpa only [hfixed] using hx
      simpa only [zero_pow (by norm_num : (2:ℕ)≠0)] using Hd.pow 2
    filter_upwards [H.eventually (eventually_le_nhds hT)] with n hn
    simpa only [hTeq n] using hn
  let Q := B*(1+C)+2*b+1
  have hQ : 0 < Q := by
    have hb : 0 < b := ha.trans_le hab
    dsimp only [Q]
    positivity
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hdim.eventually HB,Hcap,Hrad,Hsmall] with n hnMean hnCap hnRad hnSmall t ht
  let x := (M n).xs
  let r := x*t
  let u := (M n).alpha.val.val r
  let S := (M n).radiusS r
  let K := actualMixedClock (dim n+1) (M n).bf (M n).hf u
  have hr : r∈Icc (M n).data.rmin 1 := hnRad t ht
  have hu : u∈Icc (M n).data.s 1 := by
    have H := (M n).alpha.val.property.2 hr.1
    exact ⟨by simpa only [(M n).alpha.property.1] using H,
      ((M n).alpha.val.property.1 r).2⟩
  have hu0 : u∈Ioc (0:ℝ) 1 := ⟨(M n).data.hs.1.trans_le hu.1,hu.2⟩
  have hS0 : 0 ≤ S := ((M n).full_radius_moments.2.2 r).1.1
  have hr0 : 0 ≤ r := (M n).data.hrbounds.1.le.trans hr.1
  have hS : S ≤ B*(1+C)*x := by
    have Hmean := hnMean (M n) u hu0
    have Hcap' := hnCap t ht
    have Hmul := mul_le_mul_of_nonneg_left Hcap' hB.le
    dsimp only [S,ActualHighWallOverlapMinimum.radiusS,u,r,x] at *
    nlinarith only [Hmean,Hmul]
  have hK0 : 0 ≤ K := by
    dsimp only [K,actualMixedClock]
    exact add_nonneg (NNReal.coe_nonneg _)
      (mul_nonneg (NNReal.coe_nonneg _) hS0)
  have hq0 : 0 ≤ K/(T*x) := div_nonneg hK0 (mul_nonneg hT.le (M n).hxs.le)
  have Hcomp := (M n).high_mass_mixed_clock_radius_abs_le_mean_radius_abs hnSmall hu
  rw [(M n).data.wallRadius_inverse (M n).alpha hr,hTeq n] at Hcomp
  change |K/T-r| ≤ |S-r| at Hcomp
  have Habs : |S-r| ≤ S+r := by
    calc
      |S-r| ≤ |S-0|+|0-r| := abs_sub_le S 0 r
      _ = S+r := by simp [abs_of_nonneg hS0,abs_of_nonneg hr0]
  have Hq : K/T ≤ S+2*r := by
    have Hlin := le_abs_self (K/T-r)
    linarith only [Hlin,Hcomp,Habs]
  have hrb : r ≤ x*b := mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le
  have Hupper : K/T ≤ (B*(1+C)+2*b)*x := by
    calc
      K/T ≤ S+2*r := Hq
      _ ≤ B*(1+C)*x+2*(x*b) := add_le_add hS
        (mul_le_mul_of_nonneg_left hrb (by norm_num))
      _ = (B*(1+C)+2*b)*x := by ring
  have Hdiv := (div_le_iff₀ (M n).hxs).mpr Hupper
  have Hnorm : K/(T*x)=(K/T)/x := by field_simp [hT.ne',(M n).hxs.ne']
  refine ⟨hq0,?_⟩
  rw [Hnorm]
  exact Hdiv.trans (by dsimp only [Q];linarith)

end OAI.SKFluctuations.LaplaceWindowFormalization
