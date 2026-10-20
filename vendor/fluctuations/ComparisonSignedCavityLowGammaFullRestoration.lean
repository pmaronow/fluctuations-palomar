module

public import ComparisonSignedCavityLowRestorationParity

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_rest_payload_low_restore_second (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
      (fun σ=>P (T.cavityAssignment σ).1) 0=
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 1 b h K)
        (fun σ=>P (T.cavityAssignment σ).1) 0+
      (∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K T
        (fun σ=>P (T.cavityAssignment σ).1) 0 2 l 1) := by
  let J:=fun σ=>P (T.cavityAssignment σ).1
  have HT:=second_jet_remainder
    (fun l=>cutLowJet n q U b h K T J 0 0 l 1)
    (fun l=>cutLowJet n q U b h K T J 0 1 l 1)
    (fun l=>cutLowJet n q U b h K T J 0 2 l 1)
    (cutLowJet_continuous_l n q U b h K T J 0 0 1)
    (cutLowJet_continuous_l n q U b h K T J 0 1 1)
    (cutLowJet_continuous_l n q U b h K T J 0 2 1)
    (fun _ hl=>cutLowJet_hasDerivAt_l n q U hl (by norm_num : (1:ℝ)∈Icc 0 1)
      b h K hq0 hq hb hh hK hbm hhm hKm T ho J 0 0)
    (fun _ hl=>cutLowJet_hasDerivAt_l n q U hl (by norm_num : (1:ℝ)∈Icc 0 1)
      b h K hq0 hq hb hh hK hbm hhm hKm T ho J 0 1)
  rw [cutLowJet_zero n q U b h K T ho J 0 1 1,cutLowJet_zero n q U b h K T ho J 0 0 1,
    native_low_rest_only_first_derivative_zero n q U b h K T ho P hq0 hq hb hh hK hbm hhm hKm hU,
    add_zero] at HT
  exact HT

def nativeCenteredLowGammaOriginalLeading (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
       r.tree.disorderExpect (fullWeight n) (fullFeature n) 0
         (cutFullVariance n q U 1 1 b h K)
         (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
           (r.tree.cavityAssignment σ).1) 0))).sum)).sum/2

def nativeCenteredLowGammaLowRestoration (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
       (∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K r.tree
         (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
           (r.tree.cavityAssignment σ).1) 0 2 l 1)))).sum)).sum/2

theorem native_centered_low_gamma_original_leading_eq_path_add_low_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) :
    nativeCenteredLowGammaOriginalLeading n q U b h K S T P a z=
      nativeCenteredLowGammaHighPath n q U b h K S T P a z 1+
      nativeCenteredLowGammaLowRestoration n q U b h K S T P a z := by
  have Hpoint (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree):=
    native_rest_payload_low_restore_second n q U b h K r.tree ho
      (insertedRestTest P (restCenteredLowKernel n U b S) p r)
      hq0 hq hb hh hK hbm hhm hKm hU
  unfold nativeCenteredLowGammaOriginalLeading nativeCenteredLowGammaHighPath
    nativeCenteredLowGammaLowRestoration
  simp_rw [Hpoint]
  simp only [mul_add,List.sum_map_add,add_div]

theorem native_first_low_and_gamma_high_eq_original_leading (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z<U) :
    retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P [a,z]+
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z=
      nativeCenteredLowGammaOriginalLeading n q U b h K S T P a z-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z-
      nativeCenteredLowGammaLowRestoration n q U b h K S T P a z := by
  have HH:=native_first_low_and_gamma_high_eq_restored_path n q U b h K S T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz
  have HL:=native_centered_low_gamma_original_leading_eq_path_add_low_restoration n q U b h K S T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU
  linarith

end OAI.SKFluctuations.Cavity
