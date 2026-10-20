module

public import ComparisonNativeGeneralMinimumMassGeometry
public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.regularCommonGeometry
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1) :
    a.CommonBandGeometry p where
  clockRegularity := hclock
  capSet := p.contactCaps
  hopen := p.contactCaps_open
  hcapSet := fun _ hr=>hr.1.1
  hnegative := fun _ hr=>hr.1.2
  hcomponent := by
    intro r hr
    rw [p.contactCaps_component hr]
    exact ⟨hr.2,(p.negative_component_endpoints hr.1).2⟩

def Potential.shellHistoryGeometry
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm)
    (hb : ∀u,a.b u=historyMatrixClock T epsilon shell ts u)
    (hh : ∀u,a.h u=historyFieldClock ts u) : a.CommonBandGeometry p :=
  p.regularCommonGeometry (NativePullbackClockRegularity.of_shell_history
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha
    T epsilon shell ts a.b a.h hb hh le_rfl zero_le_one le_rfl)

def Potential.regularCanonicalModel
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1)
    (ell : ℕ) (hell : 2 < ell) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) : NativeBandModel :=
  ((p.regularCommonGeometry hclock).canonical v hv hv1 ell hell Q Lside hQ hLside).toModel
    dphys e hlog hnd

def Potential.regularContactDyadicFamily
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1)
    (ell : ℕ) (hell : 2 < ell+1) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d) :
    NativeContactDyadicBandFamily
      (((p.regularCommonGeometry hclock).canonical 1 zero_lt_one le_rfl
        (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd) where
  toNativeDyadicBandFamily := (p.regularCommonGeometry hclock).canonicalDyadicFamily
    ell hell Q Lside hQ hLside dphys e hlog hnd
  alpha := fun _ => rfl
  thermal := fun _ => rfl
  caps := fun _ => rfl
  massLo := fun _ => rfl
  massHi := fun _ => rfl

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
