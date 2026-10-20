module

public import ComparisonSignedCavityActualGLawRestoration
public import ComparisonSignedCavityActualFourGLinearResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_original_longitudinal_restoration_const_mul (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot) (c : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalLongitudinalRestoration n q U b h K C T (fun σ=>c*P σ) a=
      c*nativeOriginalLongitudinalRestoration n q U b h K C T P a := by
  have H:=native_original_longitudinal_law_restoration n q U b h K C T ho P a
    hq0 hq hb hh hK hbm hhm hKm
  have HC:=native_original_longitudinal_law_restoration n q U b h K C T ho (fun σ=>c*P σ) a
    hq0 hq hb hh hK hbm hhm hKm
  rw [native_original_longitudinal_const_mul_test n _ _ _ _ _ _ _ _ ho,
    native_original_longitudinal_const_mul_test n _ _ _ _ _ _ _ _ ho] at HC
  linear_combination c*H-HC

theorem native_original_longitudinal_restoration_add (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.Assignment→ℝ) (a : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalLongitudinalRestoration n q U b h K C T (fun σ=>P σ+Q σ) a=
      nativeOriginalLongitudinalRestoration n q U b h K C T P a+
      nativeOriginalLongitudinalRestoration n q U b h K C T Q a := by
  have HP:=native_original_longitudinal_law_restoration n q U b h K C T ho P a
    hq0 hq hb hh hK hbm hhm hKm
  have HQ:=native_original_longitudinal_law_restoration n q U b h K C T ho Q a
    hq0 hq hb hh hK hbm hhm hKm
  have HPQ:=native_original_longitudinal_law_restoration n q U b h K C T ho (fun σ=>P σ+Q σ) a
    hq0 hq hb hh hK hbm hhm hKm
  rw [native_original_longitudinal_add_test,native_original_longitudinal_add_test] at HPQ
  linear_combination HP+HQ-HPQ

end OAI.SKFluctuations.Cavity
