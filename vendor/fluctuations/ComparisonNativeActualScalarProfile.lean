module

public import ComparisonNativeActualProfileSequence
public import ComparisonSignedCavityActualStarCompleteProducer
public import ActualMixedClockCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem bare_total_clock_le {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) {u : ℝ} (_hu : u∈Icc (0:ℝ) 1) :
    (M.hf u:ℝ)+(M.bf u:ℝ)  ≤  T := by
  have hr := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hg0 := (laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
  have hgT := (laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
    (M.hlb.trans_eq (hb 0))
  change ((M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u).toNNReal:ℝ)+
    ((M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)).toNNReal:ℝ)  ≤  T
  rw [hh u,hb u,zero_add,Real.coe_toNNReal _ (mul_nonneg hg0 hr.1),
    Real.coe_toNNReal _ (sub_nonneg.mpr hgT)]
  nlinarith [mul_le_mul_of_nonneg_left hr.2 hg0]

theorem bare_scalar_clock_unit_bounds {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) :
    ∀u∈Icc (0:ℝ) 1,actualScalarClockQuantile T (n+1) M.bf M.hf u∈Icc (0:ℝ) 1 := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
    M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact actualScalarClockQuantile_bounds hT (n+1) (by omega) M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    (fun _ hu => M.bare_total_clock_le hb hh hu)

def bareScalarMassProfile {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) : boundedMassProfiles :=
  quantileMassProfile (actualScalarClockQuantile T (n+1) M.bf M.hf)
    (M.bare_scalar_clock_unit_bounds hT hb hh)

theorem bareScalarMassProfile_mem {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) :
    M.bareScalarMassProfile hT hb hh ∈ scalarProfiles := quantileMassProfile_mem _ _

theorem bareScalarMassProfile_right_continuous {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) (t : ℝ) :
    ContinuousWithinAt (M.bareScalarMassProfile hT hb hh).val (Ici t) t :=
  quantileMassProfile_right_continuous _ _ _

theorem bareScalarMassProfile_cdf_cap {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    {v t : ℝ} (hv : v∈Ioc (0:ℝ) 1)
    (hclock : t  <  actualMixedClock (n+1) M.bf M.hf v/T) :
    (M.bareScalarMassProfile hT hb hh).val t  ≤  v := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
    M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  apply quantileMassProfile_le_of_larger_clock _
    (actualScalarClockQuantile_monotone hT (n+1) (by omega) M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) _ ⟨hv.1.le,hv.2⟩
  simpa only [actualScalarClockQuantile_on (n+1) M.bf M.hf hv.1] using hclock

theorem actual_bare_scalar_cdf_local_caps
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (x n)^2)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    ∀R : ℝ,0 < R → ∃C : ℝ,0 ≤ C ∧ ∀ᶠn in atTop,
      ((M n).bareScalarMassProfile hT (hb n) (hh n)).val (x n*R)  ≤  C*x n := by
  intro R hR
  let A := starMassBandConstant cu Az
  let c := 3*(A/cu)/8
  let L := max 1 ((R+1)/c)
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have hc : 0 < c := by dsimp only [c];positivity
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hRL : R < c*L := by
    have H := (div_le_iff₀ hc).mp (le_max_right 1 ((R+1)/c))
    dsimp only [L]
    nlinarith only [H]
  let W := fun n => L*x n
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hxW n : x n ≤ W n := by dsimp only [W];nlinarith [hx n]
  have hW0 : Tendsto W atTop (𝓝 0) := by simpa only [mul_zero] using hx0.const_mul L
  have Hstar := eventually_actual_bare_calibrated_star hm hdelta hroom hcl hcu hAz hC0 hCt
    hT M W (fun n => (hxs n).trans (hxW n)) hW0
    (fun n => (hscale n).trans (pow_le_pow_left₀ (hx n).le (hxW n) 2)) hb hh
  have Hsmall := (hW0.const_mul (2*A)).eventually
    (eventually_le_nhds (show (2*A)*(0:ℝ) < 1 by simp))
  refine ⟨2*A*L,by positivity,?_⟩
  filter_upwards [Hstar,Hsmall] with n hn hs
  obtain ⟨p,u,hu,_,_,_,hK,_⟩ := hn
  have hu0 : 0 < u := (mul_pos hA (mul_pos hL (hx n))).trans hu.1
  have hu1 : u ≤ 1 := hu.2.le.trans hs
  have hK' : T*(c*W n)  ≤  actualMixedClock (n+1) (M n).bf (M n).hf u := by
    convert hK using 1
    dsimp only [c,A]
    ring
  have hstrict : x n*R  <  actualMixedClock (n+1) (M n).bf (M n).hf u/T := by
    apply lt_of_lt_of_le _ ((le_div_iff₀ hT).mpr (by simpa only [mul_comm] using hK'))
    dsimp only [W]
    nlinarith [mul_lt_mul_of_pos_right hRL (hx n)]
  have Hcdf := (M n).bareScalarMassProfile_cdf_cap hT (hb n) (hh n) ⟨hu0,hu1⟩ hstrict
  exact Hcdf.trans (hu.2.le.trans_eq (by dsimp only [W];ring))

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
