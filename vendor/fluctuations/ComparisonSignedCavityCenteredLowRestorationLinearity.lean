module

public import ComparisonSignedCavityActualOriginalOneStep
public import ComparisonSignedCavityHighConnectedAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

def nativeLowGammaAtFullClock (n : ℕ) (qfull : ℕ→FullCoordinate n→ℝ)
    (U : ℕ) (b K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
       r.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull
         (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
           (r.tree.cavityAssignment σ).1) 0))).sum)).sum/2

theorem native_low_gamma_at_full_clock_sub_const (n : ℕ) (qfull : ℕ→FullCoordinate n→ℝ)
    (U : ℕ) (b K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (c : ℝ) :
    nativeLowGammaAtFullClock n qfull U b K S T (fun σ=>P σ-c) a z=
      nativeLowGammaAtFullClock n qfull U b K S T P a z-
      c*nativeLowGammaAtFullClock n qfull U b K S T (fun _=>1) a z := by
  let A:=restCenteredLowKernel n U b S
  let E (P : T.cavityLeft.Assignment→ℝ) (p : MarkedPlacement T) (r : MarkedPlacement p.tree):=
    r.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull
      (fun σ=>insertedRestTest P A p r (r.tree.cavityAssignment σ).1) 0
  have HI (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      E (fun σ=>P σ-c) p r=E P p r-c*E (fun _=>1) p r := by
    dsimp only [E]
    unfold ClockTree.disorderExpect insertedRestTest
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  let Pi (p : MarkedPlacement T) (r : MarkedPlacement p.tree):=
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed p.mark) r.mark
  have HW (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      Pi p r*(E P p r-c*E (fun _=>1) p r)=Pi p r*E P p r-c*(Pi p r*E (fun _=>1) p r) := by ring
  unfold nativeLowGammaAtFullClock
  change ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*(Pi p r*E (fun σ=>P σ-c) p r))).sum)).sum/2=_
  simp_rw [HI,HW]
  rw [native_signed_double_sum_sub]
  dsimp only [E,Pi,A]
  ring

theorem native_centered_low_gamma_low_restoration_sub_const (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (c : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU : U ≤ as.length) :
    nativeCenteredLowGammaLowRestoration n q U b h K S T (fun σ=>P σ-c) a z=
      nativeCenteredLowGammaLowRestoration n q U b h K S T P a z-
      c*nativeCenteredLowGammaLowRestoration n q U b h K S T (fun _=>1) a z := by
  have HP:=native_centered_low_gamma_original_leading_eq_path_add_low_restoration n q U b h K S T ho
    P a z hq0 hq hb hh hK hbm hhm hKm hU
  have H1:=native_centered_low_gamma_original_leading_eq_path_add_low_restoration n q U b h K S T ho
    (fun _=>1) a z hq0 hq hb hh hK hbm hhm hKm hU
  have HC:=native_centered_low_gamma_original_leading_eq_path_add_low_restoration n q U b h K S T ho
    (fun σ=>P σ-c) a z hq0 hq hb hh hK hbm hhm hKm hU
  have HL:=native_low_gamma_at_full_clock_sub_const n (cutFullVariance n q U 1 1 b h K) U b K S T P a z c
  have HD:=native_low_gamma_at_full_clock_sub_const n (cutFullVariance n q U 0 1 b h K) U b K S T P a z c
  change nativeCenteredLowGammaOriginalLeading n q U b h K S T (fun σ=>P σ-c) a z=
    nativeCenteredLowGammaOriginalLeading n q U b h K S T P a z-
      c*nativeCenteredLowGammaOriginalLeading n q U b h K S T (fun _=>1) a z at HL
  change nativeCenteredLowGammaHighPath n q U b h K S T (fun σ=>P σ-c) a z 1=
    nativeCenteredLowGammaHighPath n q U b h K S T P a z 1-
      c*nativeCenteredLowGammaHighPath n q U b h K S T (fun _=>1) a z 1 at HD
  linear_combination -HC+HP-c*H1+HL-HD

theorem native_centered_low_gamma_low_restoration_original_center (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU : U ≤ as.length) :
    nativeCenteredLowGammaLowRestoration n q U b h K S T
      (nativeOriginalCenteredRestTest n q U b h K T P) a z=
      nativeCenteredLowGammaLowRestoration n q U b h K S T P a z-
      nativeOriginalRestTestExpectation n q U b h K T P*
        nativeCenteredLowGammaLowRestoration n q U b h K S T (fun _=>1) a z := by
  unfold nativeOriginalCenteredRestTest
  exact native_centered_low_gamma_low_restoration_sub_const n q U b h K S T ho P a z _
    hq0 hq hb hh hK hbm hhm hKm hU

end OAI.SKFluctuations.Cavity
