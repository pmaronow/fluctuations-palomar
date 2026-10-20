module

public import ComparisonSignedCavityActualSixConnectedClassification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000

def nativeFourConnectedKernel {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ)
    (a z e f c d : T.Slot) : ℝ :=
  fullScalarCutConnected4 T U K a c e f*fullScalarCutGamma T U K z d+
  fullScalarCutConnected4 T U K a d e f*fullScalarCutGamma T U K z c+
  fullScalarCutGamma T U K a c*fullScalarCutConnected4 T U K z d e f+
  fullScalarCutGamma T U K a d*fullScalarCutConnected4 T U K z c e f

def nativeFourConnectedLowAllocation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z e f : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest P (restLowKernel n U b h) p r) 0*
      nativeFourConnectedKernel r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed (p.embed e)) (r.embed (p.embed f)) (r.embed p.mark) r.mark)).sum)).sum/2

theorem native_low_connected_six_eq_four_allocations (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z e f : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) (hef : U ≤ T.splitIndex e f) :
    nativeLowConnectedSix n q U b h K T P a z e f=
      nativeFourConnectedLowAllocation n q U b h K T P a z e f := by
  unfold nativeLowConnectedSix nativeFourConnectedLowAllocation
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have haz' : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z)) < U := by
    rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    exact haz
  have hef' : U ≤ r.tree.splitIndex (r.embed (p.embed e)) (r.embed (p.embed f)) := by
    rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    exact hef
  by_cases hcd : r.tree.splitIndex (r.embed p.mark) r.mark < U
  · have H:=native_six_connected_complete_allocation r.tree ho U K
      (r.embed (p.embed a)) (r.embed (p.embed z))
      (r.embed (p.embed e)) (r.embed (p.embed f)) (r.embed p.mark) r.mark hU haz' hcd hef'
    change nativeSixConnectedKernel _ _ _ _ _ _ _ _ _=nativeFourConnectedKernel _ _ _ _ _ _ _ _ _ at H
    rw [←H]
    rfl
  · have H : insertedRestTest P (restLowKernel n U b h) p r=fun _=>0 := by
      funext σ
      simp only [insertedRestTest,restLowKernel,hcd,ite_false,mul_zero]
    rw [H]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero,zero_mul]

def nativeErrorFirstLowDefectLedger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark*
        retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] r.tree
          (insertedRestTest P (restHighKernel n U b h K) p r)
          [r.embed (p.embed a),r.embed (p.embed z)]))).sum)).sum/2

def nativeErrorFirstFourConnectedLedger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      nativeFourConnectedLowAllocation n q U b h K r.tree
        (insertedRestTest P (restHighKernel n U b h K) p r)
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark)).sum)).sum/2

theorem native_error_first_connected_eq_defect_and_four (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeErrorFirstConnectedLedger n q U b h K T P a z=
      nativeErrorFirstLowDefectLedger n q U b h K S T P a z+
      nativeErrorFirstFourConnectedLedger n q U b h K T P a z := by
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      nativeLowHighConnectedCoefficient n q U b h K r.tree
        (insertedRestTest P (restHighKernel n U b h K) p r)
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark=
      fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark*
        retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] r.tree
          (insertedRestTest P (restHighKernel n U b h K) p r)
          [r.embed (p.embed a),r.embed (p.embed z)]+
      nativeFourConnectedLowAllocation n q U b h K r.tree
        (insertedRestTest P (restHighKernel n U b h K) p r)
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark := by
    have haz' : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z)) < U := by
      rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
        (T.markedAttach_embed_preserves 0 p hp).2]
      exact haz
    rw [native_low_high_connected_eq_defect_and_six n q U b h K S hKS r.tree ho
      (insertedRestTest P (restHighKernel n U b h K) p r)
      (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU haz']
    by_cases hef : U ≤ r.tree.splitIndex (r.embed p.mark) r.mark
    · rw [native_low_connected_six_eq_four_allocations n q U b h K r.tree ho _
        _ _ _ _ hU haz' hef]
    · have H : insertedRestTest P (restHighKernel n U b h K) p r=fun _=>0 := by
        funext σ
        simp only [insertedRestTest,restHighKernel,lt_of_not_ge hef,ite_true,mul_zero]
      rw [H]
      simp only [nativeLowConnectedSix,nativeFourConnectedLowAllocation,
        insertedRestTest,zero_mul,ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero,
        List.map_const',List.sum_replicate,nsmul_zero,zero_div]
  unfold nativeErrorFirstConnectedLedger nativeErrorFirstLowDefectLedger nativeErrorFirstFourConnectedLedger
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        nativeLowHighConnectedCoefficient n q U b h K r.tree
          (insertedRestTest P (restHighKernel n U b h K) p r)
          (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark)).sum)=
      (T.markedAttach 0).map (fun p=>p.coeff*
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*
          (fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark*
            retainedSignedJets n q U b h K [restCenteredLowKernel n U b S] r.tree
              (insertedRestTest P (restHighKernel n U b h K) p r)
              [r.embed (p.embed a),r.embed (p.embed z)]+
          nativeFourConnectedLowAllocation n q U b h K r.tree
            (insertedRestTest P (restHighKernel n U b h K) p r)
            (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark))).sum) := by
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    rw [HI p hp r hr]
  rw [HE]
  simp only [mul_add,List.sum_map_add,add_div]

theorem actual_first_low_high_centered_eq_defect_and_four (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀ j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 1 0=
      nativeErrorFirstLowDefectLedger n q U b h K S T P a z+
      nativeErrorFirstFourConnectedLedger n q U b h K T P a z := by
  rw [actual_first_low_high_centered_eq_error_first_ledger n q U b h K T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz,
    native_error_first_connected_eq_defect_and_four n q U b h K S hKS T ho P a z hU haz]

end OAI.SKFluctuations.Cavity
