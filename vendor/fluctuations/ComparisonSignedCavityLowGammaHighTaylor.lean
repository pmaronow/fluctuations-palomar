module

public import ComparisonSignedCavityActualMixedLowDefect

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_rest_payload_high_taylor (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 1 b h K)
      (fun σ=>P (T.cavityAssignment σ).1) 0=
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0+
      retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []+
      (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K T
        (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t) := by
  let J:=fun σ=>P (T.cavityAssignment σ).1
  have HT:=second_jet_remainder
    (cutFrozenLowHighJet n q U b h K T J 0 0 0)
    (cutFrozenLowHighJet n q U b h K T J 0 0 1)
    (cutFrozenLowHighJet n q U b h K T J 0 0 2)
    (cutFrozenLowHighJet_continuous n q U b h K T J 0 0 0)
    (cutFrozenLowHighJet_continuous n q U b h K T J 0 0 1)
    (cutFrozenLowHighJet_continuous n q U b h K T J 0 0 2)
    (fun _ ht=>cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK hbm hhm hKm ho J 0 0 0 ht)
    (fun _ ht=>cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK hbm hhm hKm ho J 0 0 1 ht)
  have H0:=actual_frozen_coefficient_eq_retained n q U b h K T ho P []
    hq0 hq hb hh hK hbm hhm hKm 0 0
  have H1:=actual_frozen_coefficient_eq_retained n q U b h K T ho P []
    hq0 hq hb hh hK hbm hhm hKm 0 1
  simp only [siteMonomial,mul_one,List.replicate_zero,List.nil_append,
    retainedSignedJets,fullScalarCutMoment_nil T ho,mul_one] at H0
  simp only [siteMonomial,mul_one,List.replicate_zero,List.replicate_one,List.nil_append] at H1
  rw [cutFrozenLowHighJet_endpoint,cutLowJet_zero n q U b h K T ho J 0 0 1,H0,H1] at HT
  exact HT

def nativeCenteredLowGammaHighPath (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (t : ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
       r.tree.disorderExpect (fullWeight n) (fullFeature n) 0
         (cutFullVariance n q U 0 t b h K)
         (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
           (r.tree.cavityAssignment σ).1) 0))).sum)).sum/2

def nativeCenteredLowGammaHighSecondRemainder (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
       (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K r.tree
         (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r
           (r.tree.cavityAssignment σ).1) 0 0 2 t)))).sum)).sum/2

theorem native_centered_low_gamma_high_path_taylor (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeCenteredLowGammaHighPath n q U b h K S T P a z 1=
      nativeCenteredLowGammaHighPath n q U b h K S T P a z 0+
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z+
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z := by
  have Hpoint (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree):=
    native_rest_payload_high_taylor n q U b h K r.tree ho
      (insertedRestTest P (restCenteredLowKernel n U b S) p r)
      hq0 hq hb hh hK hbm hhm hKm
  unfold nativeCenteredLowGammaHighPath nativeCenteredLowGammaHighLedger
    nativeCenteredLowGammaHighSecondRemainder
  simp_rw [Hpoint]
  simp_rw [native_decoupled_rest_expect n q U b h K _ ho]
  simp only [mul_add,List.sum_map_add,add_div]

theorem native_first_low_and_gamma_high_eq_restored_path (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z<U) :
    retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P [a,z]+
      nativeCenteredLowGammaHighLedger n q U b h K S T P a z=
      nativeCenteredLowGammaHighPath n q U b h K S T P a z 1-
      nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z := by
  have H0:=retained_one_low_eq_gamma_allocations n q U b h K T ho P
    (restCenteredLowKernel n U b S)
    (by intro j hj σ τ;simp only [restCenteredLowKernel,not_lt.mpr hj,ite_false]) a z hU haz
  have HC : nativeCenteredLowGammaHighPath n q U b h K S T P a z 0=
      retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] T P [a,z] := by
    rw [H0]
    unfold nativeCenteredLowGammaHighPath nativeLowScalarPairing
    simp_rw [native_decoupled_rest_expect n q U b h K _ ho]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    ring
  have HT:=native_centered_low_gamma_high_path_taylor n q U b h K S T ho P a z
    hq0 hq hb hh hK hbm hhm hKm
  rw [HC] at HT
  linarith

end OAI.SKFluctuations.Cavity
