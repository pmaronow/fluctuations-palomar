module

public import ComparisonSignedCavityActualGeneratedGammaFirstHighProfile
public import ComparisonSignedCavityInheritedTwoHighRestPayloadL2

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_generated_Gamma_high_second_eq_paired_source
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A P=
      (1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
        nativeRestPayloadHighSecondIntegral n q U b h K p.tree
          (nativeRestProjectedPairedTest T P₀.live.test.target star A P p))).sum := by
  dsimp only
  unfold nativeGammaProjectedHighSecondRestoration
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hpH : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark
  · have HE:=native_actual_generated_fresh_high_jets_polarization hP hi hs ho q b h K p hp hpH
      (fun σ τ=>A σ.1 τ.1) (fun σ=>P (T.cavityAssignment σ).1)
      hq0 hq hb hh hK hbm hhm hKm 2
    have HI : (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K p.tree
        (fun σ=>nativeRestProjectedDisplacementTest T P₀.live.test.target star A P p
          (p.tree.cavityAssignment σ).1) 0 0 2 t)=
        (1/2:ℝ)*nativeRestPayloadHighSecondIntegral n q U b h K p.tree
          (nativeRestProjectedPairedTest T P₀.live.test.target star A P p) := by
      unfold nativeRestPayloadHighSecondIntegral
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      have HE':=HE t (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht)
      simp only [←native_rest_projected_displacement_test_actual,
        ←native_rest_projected_paired_test_actual] at HE'
      dsimp only
      rw [HE']
      ring
    rw [HI]
    ring
  · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hP.highCut_le_length (lt_of_not_ge hpH)]
    ring

theorem actual_minimum_generated_Gamma_high_second_eq_paired_source
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeGammaProjectedHighSecondRestoration T P₀.live.test.target star U q b h K A P=
      (1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
        nativeRestPayloadHighSecondIntegral n q U b h K p.tree
          (nativeRestProjectedPairedTest T P₀.live.test.target star A P p))).sum := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_hf_monotone hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hq : ∀j₀,Monotone (fun j=>q j j₀) := by
    intro j₀
    cases j₀ with
    | inl j₀=>exact hbm
    | inr j₀=>exact hhm
  have hq0 : ∀j j₀,0 ≤ q j j₀ := by
    intro j j₀
    cases j₀ with
    | inl j₀=>exact hb j
    | inr j₀=>exact hh j
  exact native_actual_generated_Gamma_high_second_eq_paired_source hP hi hs ho q b h K A P
    hq0 hq hb hh hK hbm hhm hKm

theorem native_rest_payload_high_second_integral_zero (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeRestPayloadHighSecondIntegral n q U b h K T (fun _=>0)=0 := by
  unfold nativeRestPayloadHighSecondIntegral
  have HE : (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K T
      (fun _=>0) 0 0 2 t)=(∫t in (0:ℝ)..1,(0:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1:=by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
    dsimp only
    rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho (fun _=>0) 0
      hq0 hq hb hh hK hbm hhm hKm 0 2 ht',ClockTree.disorderProfileJets_zero,mul_zero]
  simpa only [intervalIntegral.integral_zero] using HE

theorem actual_minimum_rest_payload_high_second_integral_zero
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeRestPayloadHighSecondIntegral n q U b h K T (fun _=>0)=0 := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_hf_monotone hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hq : ∀j₀,Monotone (fun j=>q j j₀) := by
    intro j₀
    cases j₀ with
    | inl j₀=>exact hbm
    | inr j₀=>exact hhm
  have hq0 : ∀j j₀,0 ≤ q j j₀ := by
    intro j j₀
    cases j₀ with
    | inl j₀=>exact hb j
    | inr j₀=>exact hh j
  exact native_rest_payload_high_second_integral_zero n q U b h K T ho
    hq0 hq hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
