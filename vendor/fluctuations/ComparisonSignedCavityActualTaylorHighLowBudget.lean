module

public import ComparisonSignedCavityActualConstantTransientLowProfile
public import ComparisonSignedCavityFrozenAssembly
public import CavityQuantitativeClosure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_actual_taylor_remainder_abs_le_HIGH_LOW
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (H L : ℝ) (hH : 0≤H) (hL : 0≤L)
    (hHigh : ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
      |nativeActualHigherHighPart part n q U b h K T
        (fun σ=>P (T.cavityAssignment σ).1) a z l t|≤H)
    (hLow : ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
      |nativeActualCenteredThirdLowPart n q U b h K T P a z l t|≤L) :
    |nativeActualTaylorRemainder n q U b h K T P a z|≤2*H+L/2 := by
  have HA (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 2 t|≤H:=by
    rw [native_centered_fixed_low_high_eq_frozen n q U b h K T ho P a z
      hq0 hq hb hh hK hbm hhm hKm 1 2 ht]
    simpa only [nativeActualHigherHighPart,Fin.val_one,Fin.val_zero,show (1:ℕ)≠0 by decide,ite_false,ite_true] using hHigh 0 t (by norm_num) ht 1
  have HB (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 2 1 t|≤H:=by
    rw [native_centered_fixed_low_high_eq_frozen n q U b h K T ho P a z
      hq0 hq hb hh hK hbm hhm hKm 2 1 ht]
    simpa only [nativeActualHigherHighPart,Fin.val_zero,ite_true] using hHigh 0 t (by norm_num) ht 0
  have HC (l t : ℝ) (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
      |cutCenteredMixedJet n q U b h K T P (sitePair T a z) 0 3 l t|≤H+L:=by
    have HE:=native_centered_third_transient_ledger n q U b h K T ho
      hq0 hq hb hh hK hbm hhm hKm P (sitePair T a z) 0 hl ht
    have HE' : cutCenteredMixedJet n q U b h K T P (sitePair T a z) 0 3 l t=
        nativeActualHigherHighPart 2 n q U b h K T
          (fun σ=>P (T.cavityAssignment σ).1) a z l t+
        nativeActualCenteredThirdLowPart n q U b h K T P a z l t:=by
      simpa only [nativeActualHigherHighPart,nativeCenteredTransientHighThird,
        nativeActualCenteredThirdLowPart,map_zero,add_assoc,show (2:Fin 3).val=2 from rfl,show (2:ℕ)≠0 by decide,show (2:ℕ)≠1 by decide,ite_false] using HE
    rw [HE']
    exact (abs_add_le _ _).trans (add_le_add (hHigh l t hl ht 2) (hLow l t hl ht))
  have HAI:=weighted_unit_integral_abs_le hH HA 1
  have HBI:=weighted_unit_integral_abs_le hH HB 0
  simp only [pow_one] at HAI
  simp only [pow_zero,one_mul] at HBI
  have HCI:=weighted_unit_integral_abs_le (add_nonneg hH hL)
    (fun l hl=>by
      simpa only [pow_zero,one_mul] using weighted_unit_integral_abs_le
        (add_nonneg hH hL) (HC l · hl ·) 0) 2
  have HBI' : |(1/2:ℝ)*(∫t in (0:ℝ)..1,cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 2 1 t)|≤(1/2:ℝ)*H:=by
    rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
    exact mul_le_mul_of_nonneg_left HBI (by norm_num)
  have HCI' : |(1/2:ℝ)*(∫l in (0:ℝ)..1,(1-l)^2*∫t in (0:ℝ)..1,
      cutCenteredMixedJet n q U b h K T P (sitePair T a z) 0 3 l t)|≤(1/2:ℝ)*(H+L):=by
    rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
    exact mul_le_mul_of_nonneg_left HCI (by norm_num)
  unfold nativeActualTaylorRemainder
  have Habs:=((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add HAI HBI')) HCI'))
  convert Habs using 1; ring

end OAI.SKFluctuations.Cavity
