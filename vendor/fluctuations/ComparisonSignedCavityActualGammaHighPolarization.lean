module

public import ComparisonSignedCavityOriginalGammaLawAdapter
public import ComparisonSignedCavityActualOriginalGammaPairPolarization
public import ComparisonSignedCavityDecoupledGAtomLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_frozen_high_jets_eq_of_expectation_eq
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.Assignment→ℝ) (c : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (HE : ∀t∈Icc (0:ℝ) 1,
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K) P 0=
        c*T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K) Q 0)
    (r : ℕ) : ∀t∈Icc (0:ℝ) 1,
      cutFrozenLowHighJet n q U b h K T P 0 0 r t=
        c*cutFrozenLowHighJet n q U b h K T Q 0 0 r t := by
  induction r with
  | zero=>
    intro t ht
    rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho P 0
      hq0 hq hb hh hK hbm hhm hKm 0 0 ht,
      cutFrozenLowHighJet_eq_profileJets n q U b h K T ho Q 0
        hq0 hq hb hh hK hbm hhm hKm 0 0 ht]
    simpa only [List.replicate_zero,List.nil_append,ClockTree.disorderProfileJets] using HE t ht
  | succ r ih=>
    have HI : EqOn (cutFrozenLowHighJet n q U b h K T P 0 0 (r+1))
        (fun t=>c*cutFrozenLowHighJet n q U b h K T Q 0 0 (r+1) t) (Ioo (0:ℝ) 1) := by
      intro t ht
      have HEv : cutFrozenLowHighJet n q U b h K T P 0 0 r=ᶠ[𝓝 t]
          (fun s=>c*cutFrozenLowHighJet n q U b h K T Q 0 0 r s) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact ih s ⟨hs.1.le,hs.2.le⟩
      have HP:=cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK
        hbm hhm hKm ho P 0 0 r ht
      have HQ:=(cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK
        hbm hhm hKm ho Q 0 0 r ht).const_mul c
      exact HP.unique (HQ.congr_of_eventuallyEq HEv)
    have HC:=HI.closure (cutFrozenLowHighJet_continuous n q U b h K T P 0 0 (r+1))
      (continuous_const.mul (cutFrozenLowHighJet_continuous n q U b h K T Q 0 0 (r+1)))
    rw [closure_Ioo (by norm_num : (0:ℝ)≠1)] at HC
    exact HC

theorem native_actual_generated_fresh_high_jets_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P₀.live.test.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P₀.live.test.target star).tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (r : ℕ) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    ∀t∈Icc (0:ℝ) 1,
      cutFrozenLowHighJet n q U b h K p.tree
        (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
          A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
          P (g.restrict (p.restrict σ))) 0 0 r t=
      (1/2:ℝ)*cutFrozenLowHighJet n q U b h K p.tree
        (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
          A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
          (P (g.restrict (p.restrict σ))-
            P (nativeReplaceAtSlot T P₀.live.test.target (g.restrict (p.restrict σ)) (p.spin σ))))
          0 0 r t := by
  dsimp only
  apply native_frozen_high_jets_eq_of_expectation_eq n q U b h K p.tree ho _ _ (1/2)
    hq0 hq hb hh hK hbm hhm hKm
  intro t ht
  exact native_actual_generated_original_pair_fresh_displacement_polarization hP hi hs ho
    0 (cutFullVariance n q U 0 t b h K) 0 p hp hpH A P

end OAI.SKFluctuations.Cavity
