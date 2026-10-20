module

public import ComparisonSignedCavityMixedErrorRetainedBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

def nativeMixedGammaHighCost (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ)
    (b h K : ℕ→ℝ) (e : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) : ℝ :=
  let law:=cutFullVariance n q U 0 0 b h K
  let high:=cutTSlope n U 0 b h K
  T.forkCost (fun j=>(nativeWholeLawErrorRadius n as law high j)^e)+
    (∫s,ClockTree.edgeDensity 0 as (fun j=>(nativeWholeLawErrorRadius n as law high j)^e) s)

theorem native_gamma_weighted_low_high_placement_bound (n U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves ≤ rBound) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (hU : U ≤ as.length) (haz : T.splitIndex a z<U)
    {C p Mlow Mhigh : ℝ} (hC : 0 ≤ C) (hp : 2 < p) (hMlow : 0 ≤ Mlow) (hMhigh : 0 ≤ Mhigh)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h (fun j=>h j+b j*S j))
      (fun σ=>|P (T.cavityAssignment σ).1|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))))
    (hLow : ∀σ τ : Spin n,|restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ τ| ≤ Mlow)
    (hHigh : ∀(j : ℕ) (σ τ : Spin n×Bool),
      |ReplicaTree.coordinateProfile (fullFeature n)
        (cutTSlope n U 0 b h (fun j=>h j+b j*S j)) j σ τ| ≤ Mhigh)
    (s : ClockTree.MarkedPlacement T) (hs : s∈T.markedAttach 0)
    (t : ClockTree.MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    let K:=fun j=>h j+b j*S j
    let Pi:=nativeLowScalarPairing t.tree U K (t.embed (s.embed a)) (t.embed (s.embed z))
      (t.embed s.mark) t.mark
    let dlow:=nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 0 b h K)
      (cutLowError n U b h K) (T.splitIndex a z)
    |Pi*retainedSignedJets n q U b h K [restHighKernel n U b h K] t.tree
      (insertedRestTest P (restCenteredLowKernel n U b S) s t) []| ≤
      |Pi| * (ClockTree.pairForkVariation (rBound+2)*C*Mlow^((p-2)/p)*Mhigh^((p-2)/p)*
        dlow^(2/p)*nativeMixedGammaHighCost n q U b h K (2/p) t.tree) := by
  dsimp only
  let K:=fun j=>h j+b j*S j
  let law:=cutFullVariance n q U 0 0 b h K
  let Pi:=nativeLowScalarPairing t.tree U K (t.embed (s.embed a)) (t.embed (s.embed z))
    (t.embed s.mark) t.mark
  let j₀:=T.splitIndex a z
  let Pn:=fun τ=>P (s.restRestrict (t.restRestrict τ))
  have hsEmb:=T.markedAttach_embed_preserves 0 s hs
  have htEmb:=s.tree.markedAttach_embed_preserves 0 t ht
  have hold : t.tree.splitIndex (t.embed (s.embed a)) (t.embed (s.embed z))=j₀ :=
    (htEmb.2 _ _).trans (hsEmb.2 _ _)
  have HE:=native_scalar_weighted_low_high_jet_eq_fixed_target_fork n q U b h K S T ho P a z hU haz s hs t ht
  rw [HE]
  by_cases hPi : Pi=0
  · change |Pi*_| ≤ |Pi| * _
    simp only [hPi,zero_mul,abs_zero,le_refl]
  · have hsplit : t.tree.splitIndex (t.embed s.mark) t.mark=j₀ := by
      have H:=native_low_scalar_pairing_split_weight t.tree ho U K
        (fun j=>if j=j₀ then (1:ℝ) else 0) (t.embed (s.embed a)) (t.embed (s.embed z))
        (t.embed s.mark) t.mark hU (by rw [hold];exact haz)
      rw [hold,ite_eq_left rfl,one_mul] at H
      by_contra hne
      rw [ite_eq_right hne,zero_mul] at H
      exact hPi H.symm
    have hneq : t.embed s.mark≠t.mark := by
      intro H
      rw [H,t.tree.splitIndex_self] at hsplit
      omega
    have hleaf : t.tree.leaves ≤ rBound+2 := by
      have H₁:=T.markedAttach_leaves 0 s hs
      have H₂:=s.tree.markedAttach_leaves 0 t ht
      omega
    have HPn : t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|Pn (t.tree.cavityAssignment σ).1|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))) := by
      have HM:=ClockTree.wholeLaw_double_marked_moment_eq (fullWeight_pos n) (fullFeature n)
        T ho 0 law 0 (fun σ=>P (T.cavityAssignment σ).1) (2*(p/(p-2))) s hs t ht
      have heq : (fun σ=>|Pn (t.tree.cavityAssignment σ).1|^(2*(p/(p-2))))=
          fun σ=>|P (T.cavityAssignment (s.restrict (t.restrict σ))).1|^(2*(p/(p-2))) := by
        funext σ
        simp only [Pn,t.restRestrict_actual,s.restRestrict_actual]
      rw [heq,HM]
      exact hP
    have Hjet:=native_retained_high_fixed_low_error_wholeLaw_bound n U q b h S t.tree ho hleaf Pn
      (t.embed s.mark) t.mark hneq (by rw [hsplit];exact haz)
      hC hp hMlow hMhigh HPn (by rw [hsplit];exact hLow) hHigh
    dsimp only at Hjet
    rw [hsplit] at Hjet
    have heq : insertedRestTest P (restCenteredFixedForkKernel n b S j₀) s t=
        nativeFixedLowRestPayload n t.tree Pn b S j₀ (t.embed s.mark) t.mark := by
      funext τ
      simp only [insertedRestTest,nativeFixedLowRestPayload,Pn,restCenteredFixedForkKernel,
        ClockTree.MarkedPlacement.restSpin,t.restRestrict_at]
    change |Pi*retainedSignedJets n q U b h K [restHighKernel n U b h K] t.tree
      (insertedRestTest P (restCenteredFixedForkKernel n b S j₀) s t) []| ≤ _
    rw [heq,abs_mul]
    exact mul_le_mul_of_nonneg_left Hjet (abs_nonneg Pi)

def nativeMixedGammaWeightedHighBudget (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ)
    (b h K : ℕ→ℝ) (e : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (a z : T.Slot) : ℝ :=
  T.pairAbsSum (fun s t=>
    |nativeLowScalarPairing t.tree U K (t.embed (s.embed a)) (t.embed (s.embed z))
      (t.embed s.mark) t.mark| * nativeMixedGammaHighCost n q U b h K e t.tree)

theorem native_centered_low_gamma_high_ledger_wholeLaw_bound (n U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves ≤ rBound) (P : T.cavityLeft.Assignment→ℝ)
    (a z : T.Slot) (hU : U ≤ as.length) (haz : T.splitIndex a z<U)
    {C p Mlow Mhigh : ℝ} (hC : 0 ≤ C) (hp : 2 < p) (hMlow : 0 ≤ Mlow) (hMhigh : 0 ≤ Mhigh)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h (fun j=>h j+b j*S j))
      (fun σ=>|P (T.cavityAssignment σ).1|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))))
    (hLow : ∀σ τ : Spin n,|restCenteredFixedForkKernel n b S (T.splitIndex a z) 0 σ τ| ≤ Mlow)
    (hHigh : ∀(j : ℕ) (σ τ : Spin n×Bool),
      |ReplicaTree.coordinateProfile (fullFeature n)
        (cutTSlope n U 0 b h (fun j=>h j+b j*S j)) j σ τ| ≤ Mhigh) :
    let K:=fun j=>h j+b j*S j
    let dlow:=nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 0 b h K)
      (cutLowError n U b h K) (T.splitIndex a z)
    |nativeCenteredLowGammaHighLedger n q U b h K S T P a z| ≤
      ClockTree.pairForkVariation (rBound+2)*C*Mlow^((p-2)/p)*Mhigh^((p-2)/p)*
        dlow^(2/p)*nativeMixedGammaWeightedHighBudget n q U b h K (2/p) T a z/2 := by
  dsimp only
  let K:=fun j=>h j+b j*S j
  let dlow:=nativeWholeLawErrorRadius n as (cutFullVariance n q U 0 0 b h K)
    (cutLowError n U b h K) (T.splitIndex a z)
  let V:=ClockTree.pairForkVariation (rBound+2)*C*Mlow^((p-2)/p)*Mhigh^((p-2)/p)*dlow^(2/p)
  let F:=fun (s : ClockTree.MarkedPlacement T) (t : ClockTree.MarkedPlacement s.tree)=>
    nativeLowScalarPairing t.tree U K (t.embed (s.embed a)) (t.embed (s.embed z))
      (t.embed s.mark) t.mark*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] t.tree
        (insertedRestTest P (restCenteredLowKernel n U b S) s t) []
  have H:=T.signedPair_abs_le_pairAbsSum F
  have HB : T.pairAbsSum (fun s t=>|F s t|) ≤
      V*nativeMixedGammaWeightedHighBudget n q U b h K (2/p) T a z := by
    rw [nativeMixedGammaWeightedHighBudget,←T.pairAbsSum_const_mul]
    apply T.pairAbsSum_mono
    intro s hs t ht
    have HP:=native_gamma_weighted_low_high_placement_bound n U q b h S T ho hT P a z hU haz
      hC hp hMlow hMhigh hP hLow hHigh s hs t ht
    dsimp only at HP
    simpa only [F,V,dlow,K,mul_assoc,mul_left_comm,mul_comm] using HP
  have Htotal:=H.trans HB
  change |_/2| ≤ _
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  exact div_le_div_of_nonneg_right Htotal (by norm_num)

end OAI.SKFluctuations.Cavity
