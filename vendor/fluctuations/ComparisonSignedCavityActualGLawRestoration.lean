module

public import ComparisonSignedCavityActualOriginalGPairingTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000

def nativeActualLawRestorationRemainder (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ) : ℝ :=
  (∫t in (0:ℝ)..1,cutMixedJet n q U b h K T P 0 0 0 t)+
    ∫l in (0:ℝ)..1,cutLowJet n q U b h K T P 0 1 l 1

theorem actual_original_law_eq_decoupled_add_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K) P 0=
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K) P 0+
      nativeActualLawRestorationRemainder n q U b h K T P := by
  have HL:=first_jet_remainder
    (fun l=>cutLowJet n q U b h K T P 0 0 l 1)
    (fun l=>cutLowJet n q U b h K T P 0 1 l 1)
    (cutLowJet_continuous_l n q U b h K T P 0 0 1)
    (cutLowJet_continuous_l n q U b h K T P 0 1 1)
    (fun l hl=>cutLowJet_hasDerivAt_l n q U hl (by norm_num) b h K
      hq0 hq hb hh hK hbm hhm hKm T ho P 0 0)
  have HT:=first_jet_remainder
    (cutLowJet n q U b h K T P 0 0 0)
    (cutMixedJet n q U b h K T P 0 0 0)
    (cutLowJet_continuous_t n q U b h K T P 0 0 0)
    (cutMixedJet_continuous_t n q U b h K T P 0 0 0)
    (fun t ht=>cutLowJet_hasDerivAt_t n q U (by norm_num) ht b h K
      hq0 hq hb hh hK hbm hhm hKm T ho P 0 0)
  rw [cutLowJet_zero n q U b h K T ho P 0 1 1,
    cutLowJet_zero n q U b h K T ho P 0 0 1] at HL
  rw [cutLowJet_zero n q U b h K T ho P 0 0 1,
    cutLowJet_zero n q U b h K T ho P 0 0 0] at HT
  unfold nativeActualLawRestorationRemainder
  linarith

def nativeOriginalLongitudinalRestoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (a : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      ((r.tree.markedAttach 0).map (fun z=>z.coeff*
        nativeActualLawRestorationRemainder n q U b h K z.tree
          (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*
            nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
              (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ))).sum)).sum)).sum

theorem native_original_longitudinal_law_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b C T P a=
      nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 0 0 b h K) 0 U K b C T P a+
      nativeOriginalLongitudinalRestoration n q U b h K C T P a := by
  unfold nativeOriginalLongitudinalPairing nativeOriginalLongitudinalRestoration
  simp_rw [actual_original_law_eq_decoupled_add_restoration n q U b h K _ ho _
    hq0 hq hb hh hK hbm hhm hKm]
  simp only [mul_add,List.sum_map_add]

theorem native_original_longitudinal_eq_retained_add_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) (hU : U ≤ as.length)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b C T
      (fun σ=>P (T.cavityAssignment σ).1) a=
      nativeRetainedLongitudinalPairing n q U b h K T P a+
      nativeOriginalLongitudinalRestoration n q U b h K C T
        (fun σ=>P (T.cavityAssignment σ).1) a := by
  rw [native_original_longitudinal_law_restoration n q U b h K C T ho _ a
      hq0 hq hb hh hK hbm hhm hKm,
    ←native_retained_longitudinal_eq_decoupled_original_L n q U b h K C hKC T ho P a hU]

end OAI.SKFluctuations.Cavity
