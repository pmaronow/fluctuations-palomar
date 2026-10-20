module

public import ComparisonNativeRegularBandGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem exists_actual_common_geometry_regular
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hq : 2 ≤ a.context.N^delta)
    (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1) :
    ∃p : a.Potential, Nonempty (a.CommonBandGeometry p) := by
  obtain ⟨p⟩ := a.exists_potential hq
  exact ⟨p, ⟨p.regularCommonGeometry hclock⟩⟩

theorem eventually_exists_actual_common_geometry_regular
    (hdelta : 0 < delta) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∃p : a.Potential, Nonempty (a.CommonBandGeometry p) := by
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hp : ∀ᶠn : ℕ in atTop, 2 ≤ (n+1 : ℝ)^delta := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (((tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop).comp hshift).eventually
        (eventually_ge_atTop 2)
  filter_upwards [hp] with n hn
  intro a hclock
  exact a.exists_actual_common_geometry_regular
    (by simpa only [NativeOverlapContext.N, Nat.cast_add, Nat.cast_one] using hn) hclock

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
