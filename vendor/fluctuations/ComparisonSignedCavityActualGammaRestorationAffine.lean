module

public import ComparisonSignedCavityActualGammaFirstHighPairedSource
public import ComparisonSignedCavityActualOriginalGammaPairPolarization
public import ComparisonSignedCavityDecoupledGAtomLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_low_jets_eq_of_expectation_eq
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.Assignment→ℝ) (c : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (HE : ∀t∈Icc (0:ℝ) 1,
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U t 1 b h K) P 0=
        c*T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U t 1 b h K) Q 0)
    (r : ℕ) : ∀t∈Icc (0:ℝ) 1,
      cutLowJet n q U b h K T P 0 r t 1=
        c*cutLowJet n q U b h K T Q 0 r t 1 := by
  induction r with
  | zero=>
    intro t ht
    rw [cutLowJet_zero n q U b h K T ho P 0 t 1,
      cutLowJet_zero n q U b h K T ho Q 0 t 1]
    exact HE t ht
  | succ r ih=>
    have HI : EqOn (cutLowJet n q U b h K T P 0 (r+1) · 1)
        (fun t=>c*cutLowJet n q U b h K T Q 0 (r+1) t 1) (Ioo (0:ℝ) 1) := by
      intro t ht
      have HEv : (fun t=>cutLowJet n q U b h K T P 0 r t 1)=ᶠ[𝓝 t]
          (fun s=>c*cutLowJet n q U b h K T Q 0 r s 1) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact ih s ⟨hs.1.le,hs.2.le⟩
      have HP:=cutLowJet_hasDerivAt_l n q U (t:=1) ht (by norm_num) b h K hq0 hq hb hh hK
        hbm hhm hKm T ho P 0 r
      have HQ:=(cutLowJet_hasDerivAt_l n q U (t:=1) ht (by norm_num) b h K hq0 hq hb hh hK
        hbm hhm hKm T ho Q 0 r).const_mul c
      exact HP.unique (HQ.congr_of_eventuallyEq HEv)
    have HC:=HI.closure (cutLowJet_continuous_l n q U b h K T P 0 (r+1) 1)
      (continuous_const.mul (cutLowJet_continuous_l n q U b h K T Q 0 (r+1) 1))
    rw [closure_Ioo (by norm_num : (0:ℝ)≠1)] at HC
    exact HC

theorem native_actual_generated_fresh_displacement_affine_expectation
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P₀.live.test.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P₀.live.test.target star).tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) (α c : ℝ) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
        (α*P (g.restrict (p.restrict σ))+c)) x=
      α*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
          A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ)))*
          P (g.restrict (p.restrict σ))) x := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
  let D:=fun σ : p.tree.Assignment=>A (p.spin σ) (g.spin (p.restrict σ))-
    A (T.atSlot (g.restrict (p.restrict σ)) P₀.live.test.target) (g.spin (p.restrict σ))
  let Q:=fun σ : p.tree.Assignment=>D σ*(P (g.restrict (p.restrict σ))-
    P (nativeReplaceAtSlot T P₀.live.test.target (g.restrict (p.restrict σ)) (p.spin σ)))
  have HP:=native_actual_generated_original_pair_fresh_displacement_polarization hP hi hs ho
    v q x p hp hpH A (fun σ=>α*P σ+c)
  have H0:=native_actual_generated_original_pair_fresh_displacement_polarization hP hi hs ho
    v q x p hp hpH A P
  have HE : (fun σ : p.tree.Assignment=>D σ*
      ((α*P (g.restrict (p.restrict σ))+c)-
        (α*P (nativeReplaceAtSlot T P₀.live.test.target (g.restrict (p.restrict σ)) (p.spin σ))+c)))=
      fun σ=>α*Q σ := by
    funext σ
    dsimp only [Q]
    ring
  change p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>D σ*(α*P (g.restrict (p.restrict σ))+c)) x=
      (1/2:ℝ)*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>D σ*((α*P (g.restrict (p.restrict σ))+c)-
          (α*P (nativeReplaceAtSlot T P₀.live.test.target (g.restrict (p.restrict σ)) (p.spin σ))+c))) x at HP
  rw [HE] at HP
  have Hmul : p.tree.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>α*Q σ) x=
      α*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q Q x := by
    unfold ClockTree.disorderExpect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [Hmul] at HP
  change p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>D σ*P (g.restrict (p.restrict σ))) x=
      (1/2:ℝ)*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q Q x at H0
  change p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>D σ*(α*P (g.restrict (p.restrict σ))+c)) x=
      α*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>D σ*P (g.restrict (p.restrict σ))) x
  rw [HP,H0]
  ring

theorem native_actual_generated_fresh_rest_affine_expectation
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P₀.live.test.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P₀.live.test.target star).tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) (α c : ℝ) :
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A
        (fun τ=>α*P τ+c) p (p.tree.cavityAssignment σ).1) x=
      α*p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p
          (p.tree.cavityAssignment σ).1) x := by
  simp_rw [native_rest_projected_displacement_test_actual]
  exact native_actual_generated_fresh_displacement_affine_expectation hP hi hs ho v q x p hp hpH
    (fun σ τ=>A σ.1 τ.1) (fun σ=>P (T.cavityAssignment σ).1) α c

theorem native_actual_generated_gamma_restorations_affine
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) (α c : ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A
        (fun σ=>α*P σ+c)=
      α*nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A P ∧
    nativeGammaProjectedLowSecondRestoration T P₀.live.test.target star U q b h K A
        (fun σ=>α*P σ+c)=
      α*nativeGammaProjectedLowSecondRestoration T P₀.live.test.target star U q b h K A P := by
  let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
  have HE (p : MarkedPlacement g.tree) (hp : p∈g.tree.markedAttach 0)
      (hpH : U≤p.tree.splitIndex (p.embed (g.embed P₀.live.test.target)) p.mark)
      (l t : ℝ) :
      p.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
        (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A
          (fun τ=>α*P τ+c) p (p.tree.cavityAssignment σ).1) 0=
      α*p.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
        (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p
          (p.tree.cavityAssignment σ).1) 0 :=
    native_actual_generated_fresh_rest_affine_expectation hP hi hs ho 0 _ 0 p hp hpH A P α c
  constructor
  · unfold nativeGammaProjectedHighSecondRestoration
    dsimp only
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    by_cases hpH : U≤p.tree.splitIndex (p.embed (g.embed P₀.live.test.target)) p.mark
    · have H:=native_frozen_high_jets_eq_of_expectation_eq n q U b h K p.tree ho _ _ α
        hq0 hq hb hh hK hbm hhm hKm (fun t _=>HE p hp hpH 0 t) 2
      have HI : (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K p.tree
          (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A
            (fun τ=>α*P τ+c) p (p.tree.cavityAssignment σ).1) 0 0 2 t)=
          α*(∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K p.tree
            (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p
              (p.tree.cavityAssignment σ).1) 0 0 2 t) := by
        rw [←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [H t (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht)]
        ring
      rw [HI]
      ring
    · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hP.highCut_le_length (lt_of_not_ge hpH)]
      ring
  · unfold nativeGammaProjectedLowSecondRestoration
    dsimp only
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    by_cases hpH : U≤p.tree.splitIndex (p.embed (g.embed P₀.live.test.target)) p.mark
    · have H:=native_low_jets_eq_of_expectation_eq n q U b h K p.tree ho _ _ α
        hq0 hq hb hh hK hbm hhm hKm (fun l _=>HE p hp hpH l 1) 2
      have HI : (∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K p.tree
          (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A
            (fun τ=>α*P τ+c) p (p.tree.cavityAssignment σ).1) 0 2 l 1)=
          α*(∫l in (0:ℝ)..1,(1-l)*cutLowJet n q U b h K p.tree
            (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p
              (p.tree.cavityAssignment σ).1) 0 2 l 1) := by
        rw [←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro l hl
        dsimp only
        rw [H l (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hl)]
        ring
      rw [HI]
      ring
    · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hP.highCut_le_length (lt_of_not_ge hpH)]
      ring

def nativeGammaProjectedSecondRestoration {n : ℕ} {as : List PositiveMass}
    (high : Bool) (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  if high then nativeGammaProjectedHighSecondRestoration T s star U q b h K A P
  else nativeGammaProjectedLowSecondRestoration T s star U q b h K A P

theorem native_actual_generated_gamma_second_restoration_affine
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) (α c : ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (high : Bool) :
    nativeGammaProjectedSecondRestoration high T P₀.live.test.target star U q b h K A
        (fun σ=>α*P σ+c)=
      α*nativeGammaProjectedSecondRestoration high T P₀.live.test.target star U q b h K A P := by
  have H:=native_actual_generated_gamma_restorations_affine hP hi hs ho q b h K A P α c
    hq0 hq hb hh hK hbm hhm hKm
  cases high with
  | false=>exact H.2
  | true=>exact H.1

end OAI.SKFluctuations.Cavity
