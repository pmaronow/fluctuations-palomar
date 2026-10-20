module

public import ComparisonNativeActualMinimumMassBudgets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.generalCanonicalModel
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1))
    (ell : ℕ) (hell : 2 < ell) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) : NativeBandModel :=
  ((p.commonGeometry Kb Kh hparent hfield).canonical v hv hv1 ell hell Q Lside hQ hLside).toModel
    dphys e hlog hnd

def Potential.generalContactDyadicFamily
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1))
    (ell : ℕ) (hell : 2 < ell+1) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d) :
    NativeContactDyadicBandFamily
      (((p.commonGeometry Kb Kh hparent hfield).canonical 1 zero_lt_one le_rfl
        (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd) where
  toNativeDyadicBandFamily := (p.commonGeometry Kb Kh hparent hfield).canonicalDyadicFamily
    ell hell Q Lside hQ hLside dphys e hlog hnd
  alpha := fun _ => rfl
  thermal := fun _ => rfl
  caps := fun _ => rfl
  massLo := fun _ => rfl
  massHi := fun _ => rfl

theorem exists_actual_common_geometry_lipschitz
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hq : 2 ≤ a.context.N^delta) (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1)) :
    ∃p : a.Potential, Nonempty (a.CommonBandGeometry p) := by
  obtain ⟨p⟩ := a.exists_potential hq
  exact ⟨p, ⟨p.commonGeometry Kb Kh hparent hfield⟩⟩

theorem eventually_exists_actual_common_geometry_lipschitz
    (hdelta : 0 < delta) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1) →
      LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1) →
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
  intro a Kb Kh hparent hfield
  exact a.exists_actual_common_geometry_lipschitz
    (by simpa only [NativeOverlapContext.N, Nat.cast_add, Nat.cast_one] using hn) Kb Kh hparent hfield

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
