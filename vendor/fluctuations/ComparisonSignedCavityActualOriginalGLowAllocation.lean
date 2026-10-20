module

public import ComparisonSignedCavityActualOriginalGPairRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 20000000

def nativeOriginalGKernelLowAllocation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (A : ℕ→Spin n→Spin n→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeOriginalHighPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed a)) (r.embed p.mark)+
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeOriginalHighPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed a)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          nativeOriginalHighPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed z)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          nativeOriginalHighPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed z)) (r.embed p.mark)))).sum)).sum/2

def nativeOriginalGKernelLowRestoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (A : ℕ→Spin n→Spin n→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeOriginalHighPairRestoration n q U b h K S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed a)) (r.embed p.mark)+
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeOriginalHighPairRestoration n q U b h K S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed a)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          nativeOriginalHighPairRestoration n q U b h K S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed z)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          nativeOriginalHighPairRestoration n q U b h K S r.tree
            (insertedRestTest P A p r) (r.embed (p.embed z)) (r.embed p.mark)))).sum)).sum/2

theorem native_original_G_low_allocation_eq_retained_add_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (A : ℕ→Spin n→Spin n→ℝ)
    (hU : U ≤ as.length)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalGKernelLowAllocation n q U b h K S T P a z A=
      nativeGKernelLowAllocation n q U b h K T P a z A+
      nativeOriginalGKernelLowRestoration n q U b h K S T P a z A := by
  unfold nativeOriginalGKernelLowAllocation nativeGKernelLowAllocation nativeOriginalGKernelLowRestoration
  simp_rw [native_original_high_pairing_eq_retained_add_restoration n q U b h K S hKS _ ho _ _ _ hU
    hq0 hq hb hh hK hbm hhm hKm]
  simp only [mul_add,List.sum_map_add,add_div]
  ring

theorem native_original_G_centered_low_allocation_eq_fixed_target_fork (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeOriginalGKernelLowAllocation n q U b h K S T P a z (restCenteredLowKernel n U b S)=
      nativeOriginalGKernelLowAllocation n q U b h K S T P a z
        (restCenteredFixedForkKernel n b S (T.splitIndex a z)) := by
  unfold nativeOriginalGKernelLowAllocation
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have HS : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
    rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  have hrev : r.tree.splitIndex (r.embed (p.embed z)) (r.embed (p.embed a)) < U := by
    rw [r.tree.splitIndex_symm,HS]
    exact haz
  have H₁:=native_original_G_Gamma_centered_low_test_eq_target_split n 0 (cutFullVariance n q U 1 1 b h K) 0 U b K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [HS])
  have H₂:=native_original_G_Gamma_centered_low_test_eq_target_split n 0 (cutFullVariance n q U 1 1 b h K) 0 U b K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed a)) (r.embed (p.embed z)) r.mark (r.embed p.mark) hU (by rwa [HS])
  have H₃:=native_original_G_Gamma_centered_low_test_eq_target_split n 0 (cutFullVariance n q U 1 1 b h K) 0 U b K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed z)) (r.embed (p.embed a)) r.mark (r.embed p.mark) hU hrev
  have H₄:=native_original_G_Gamma_centered_low_test_eq_target_split n 0 (cutFullVariance n q U 1 1 b h K) 0 U b K S r.tree ho
    (fun σ=>P (p.restRestrict (r.restRestrict σ)))
    (fun σ=>p.restSpin (r.restRestrict σ)) r.restSpin
    (r.embed (p.embed z)) (r.embed (p.embed a)) (r.embed p.mark) r.mark hU hrev
  rw [r.tree.splitIndex_symm r.mark (r.embed p.mark)] at H₂ H₃
  rw [r.tree.splitIndex_symm (r.embed (p.embed z)) (r.embed (p.embed a))] at H₃ H₄
  rw [HS] at H₁ H₂ H₃ H₄
  have HEQ (A : ℕ→Spin n→Spin n→ℝ) : insertedRestTest P A p r=
      fun σ=>P (p.restRestrict (r.restRestrict σ))*
        A (r.tree.splitIndex (r.embed p.mark) r.mark) (p.restSpin (r.restRestrict σ)) (r.restSpin σ) := rfl
  rw [HEQ (restCenteredLowKernel n U b S),
    HEQ (restCenteredFixedForkKernel n b S (T.splitIndex a z))]
  linear_combination r.coeff*(H₁+H₂+H₃+H₄)

end OAI.SKFluctuations.Cavity
