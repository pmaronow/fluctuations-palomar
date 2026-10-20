module

public import ComparisonActualHighWallContinuumClockMass
public import ComparisonSignedCavityInheritedScalarFourRawScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000

theorem actual_high_wall_high_mass_le_radius
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hwork : M.xs=M.data.d) (as : List PositiveMass) (ho : MassOrdered 0 as) (j : ℕ)
    (hxv : M.xs ≤ M.data.wallRadius M.alpha (partitionPoint 0 as j))
    (hzv : M.z ≤ M.data.wallRadius M.alpha (partitionPoint 0 as j)) :
    partitionPoint 0 as j ≤ cu*M.data.wallRadius M.alpha (partitionPoint 0 as j) := by
  let u:=partitionPoint 0 as j
  let v:=M.data.wallRadius M.alpha u
  have hu:=partitionPoint_mem as ho j
  have hv:=M.data.wallRadius_bounds M.alpha u
  have hrmin : M.data.rmin < v:=by
    have Hd:=M.data.hrbounds.2.1
    rw [hwork] at hxv
    change M.data.d ≤ v at hxv
    nlinarith only [Hd,hxv,M.data.hd]
  have hhigh : M.data.s ≤ u:=(M.data.wallRadius_high_mass M.alpha hrmin).le
  have H:=(M.regular v ⟨hzv,hv.2⟩).2
  rw [M.data.wallRadius_spec M.alpha ⟨hhigh,hu.2⟩] at H
  exact H

theorem eventually_actual_high_wall_scalar_four_raw_scale_bound
    (r : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀as : List PositiveMass,MassOrdered 0 as →
      ∀(T : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U → T.leaves ≤ r →
      ∀a c e f : T.Slot,a ≠ c → U ≤ T.splitIndex a c →
      let v:=M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex a c))
      M.xs ≤ v → M.z ≤ v →
      |fullScalarCutConnected4 T U (nativeContinuumMixedClock n M.bf M.hf as) a c e f| *
        (M.xs+partitionPoint 0 as (T.splitIndex e f)) ≤ C*v := by
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_high_wall_continuum_clock_mass_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cr:=errorJetVariation r 0 0*((r:ℝ)+1)+1
  have hCr : 0 < Cr:=by
    have HH:=errorJetVariation_nonneg r 0 0
    dsimp only [Cr]
    positivity
  let Cg:=Cr*CK*(1+cu)
  have hCg : 0 < Cg:=by dsimp only [Cg];positivity
  refine ⟨2*(1+cu)+2*Cg,by positivity,?_⟩
  filter_upwards [HK] with n hn
  intro M hwork as ho T U hU hT a c e f hac hUac
  dsimp only
  intro hxv hzv
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let j:=T.splitIndex a c
  let je:=T.splitIndex e f
  let v:=M.data.wallRadius M.alpha (partitionPoint 0 as j)
  have hv0 : 0 ≤ v:=M.hxs.le.trans hxv
  have hraw0 : 0 ≤ M.xs+partitionPoint 0 as je:=add_nonneg M.hxs.le (partitionPoint_mem as ho je).1
  have Hmass:=actual_high_wall_high_mass_le_radius M hwork as ho j hxv hzv
  by_cases hdeep : j < je
  · have Hclock:=hn M hwork as ho j
    have Hsum : M.xs+partitionPoint 0 as j ≤ (1+cu)*v:=by linarith only [hxv,Hmass]
    have HKv : K j ≤ CK*(1+cu)*v:=Hclock.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hsum hCK.le)
    have Hκ:=native_full_scalar_four_deeper_split_abs_le_clock T ho r hT U hU K
      (native_continuum_mixed_clock_monotone n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho)
      (native_continuum_mixed_clock_nonneg n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho)
      a c e f hac hUac hdeep
    have Hκv : |fullScalarCutConnected4 T U K a c e f| ≤ Cg*v:=Hκ.trans (by
      change Cr*K j ≤ Cg*v
      simpa only [Cg,mul_assoc] using mul_le_mul_of_nonneg_left HKv hCr.le)
    have hraw : M.xs+partitionPoint 0 as je ≤ 2:=by
      rw [hwork]
      linarith only [M.data.hd1,(partitionPoint_mem as ho je).2]
    have HH:=mul_le_mul Hκv hraw hraw0 (mul_nonneg hCg.le hv0)
    apply HH.trans
    change Cg*v*2 ≤ (2*(1+cu)+2*Cg)*v
    nlinarith only [mul_nonneg (by positivity : 0 ≤ 2*(1+cu)) hv0]
  · have hje : je ≤ j:=Nat.le_of_not_gt hdeep
    have Hmono:=partitionPoint_mono as ho hje
    have hraw : M.xs+partitionPoint 0 as je ≤ (1+cu)*v:=by linarith only [hxv,Hmass,Hmono]
    have Hκ:=native_full_scalar_connected_four_abs_le_two T ho U K a c e f
    have HH:=mul_le_mul Hκ hraw hraw0 (by norm_num : (0:ℝ) ≤ 2)
    apply HH.trans
    change 2*((1+cu)*v) ≤ (2*(1+cu)+2*Cg)*v
    nlinarith only [mul_nonneg hCg.le hv0]

end OAI.SKFluctuations.Cavity
