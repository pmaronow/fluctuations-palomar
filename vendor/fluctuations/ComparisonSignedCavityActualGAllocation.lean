module

public import ComparisonSignedCavityActualLowHighAllocation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9000000

theorem sum_map_weight_const {A : Type*} (L : List A) (w F : A→ℝ) (c : ℝ) :
    (L.map (fun x=>w x*(c*F x))).sum=c*(L.map (fun x=>w x*F x)).sum := by
  have H : L.map (fun x=>w x*(c*F x))=L.map (fun x=>c*(w x*F x)) := by
    apply List.map_congr_left
    intro x hx
    ring
  rw [H,List.sum_map_mul_left]

def nativeLowScalarPairing {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ)
    (a z c d : T.Slot) : ℝ :=
  fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d+
    fullScalarCutGamma T U K a d*fullScalarCutGamma T U K z c

theorem fullScalarCutMoment_six_high_last {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a z c d e f : T.Slot) :
    fullScalarCutMoment T U K [a,z,c,d,e,f]=fullScalarCutMoment T U K [a,z,e,f,c,d] := by
  unfold fullScalarCutMoment scalarCutMoment
  congr 1
  funext σ
  simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
  ring

theorem native_retained_high_four_eq_scalar_and_G (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z c d : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) (hcd : T.splitIndex c d < U) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] T P [a,z,c,d]=
      nativeLowScalarPairing T U K a z c d*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []+
      fullScalarCutGamma T U K z d*nativeRetainedHighPairing n q U b h K T P a c+
      fullScalarCutGamma T U K z c*nativeRetainedHighPairing n q U b h K T P a d+
      fullScalarCutGamma T U K a c*nativeRetainedHighPairing n q U b h K T P z d+
      fullScalarCutGamma T U K a d*nativeRetainedHighPairing n q U b h K T P z c := by
  rw [←native_connected_high_pairing_eq_retained n q U b h K T ho P a c,
    ←native_connected_high_pairing_eq_retained n q U b h K T ho P a d,
    ←native_connected_high_pairing_eq_retained n q U b h K T ho P z d,
    ←native_connected_high_pairing_eq_retained n q U b h K T ho P z c]
  let R:=fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restHighKernel n U b h K) p r) 0
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      R p r*fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,c,d] p r)=
      nativeLowScalarPairing T U K a z c d*
        (R p r*fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r))+
      fullScalarCutGamma T U K z d*(R p r*fullScalarCutConnected4 r.tree U K
        (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark)+
      fullScalarCutGamma T U K z c*(R p r*fullScalarCutConnected4 r.tree U K
        (r.embed (p.embed a)) (r.embed (p.embed d)) (r.embed p.mark) r.mark)+
      fullScalarCutGamma T U K a c*(R p r*fullScalarCutConnected4 r.tree U K
        (r.embed (p.embed z)) (r.embed (p.embed d)) (r.embed p.mark) r.mark)+
      fullScalarCutGamma T U K a d*(R p r*fullScalarCutConnected4 r.tree U K
        (r.embed (p.embed z)) (r.embed (p.embed c)) (r.embed p.mark) r.mark) := by
    by_cases hef : U ≤ r.tree.splitIndex (r.embed p.mark) r.mark
    · have haz' : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z)) < U := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
          (T.markedAttach_embed_preserves 0 p hp).2]
        exact haz
      have hcd' : r.tree.splitIndex (r.embed (p.embed c)) (r.embed (p.embed d)) < U := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
          (T.markedAttach_embed_preserves 0 p hp).2]
        exact hcd
      have HS:=native_six_connected_complete_allocation r.tree ho U K
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
        (r.embed (p.embed c)) (r.embed (p.embed d)) hU haz' hcd' hef
      unfold nativeSixConnectedKernel at HS
      rw [fullScalarCutGamma_double_preserves T ho U K a c p hp r hr,
        fullScalarCutGamma_double_preserves T ho U K a d p hp r hr,
        fullScalarCutGamma_double_preserves T ho U K z c p hp r hr,
        fullScalarCutGamma_double_preserves T ho U K z d p hp r hr] at HS
      simp only [insertedSiteSlots,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
      rw [fullScalarCutMoment_six_high_last]
      unfold nativeLowScalarPairing
      unfold fullScalarCutGamma at HS ⊢
      linear_combination R p r * HS
    · have H : insertedRestTest P (restHighKernel n U b h K) p r=fun _=>0 := by
        funext σ
        simp only [insertedRestTest,restHighKernel,lt_of_not_ge hef,ite_true,mul_zero]
      have HR : R p r=0 := by
        dsimp only [R]
        rw [H]
        simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      rw [HR]
      ring
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        (R p r*fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,c,d] p r)))).sum)=
    (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        (nativeLowScalarPairing T U K a z c d*
          (R p r*fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r))+
        fullScalarCutGamma T U K z d*(R p r*fullScalarCutConnected4 r.tree U K
          (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark)+
        fullScalarCutGamma T U K z c*(R p r*fullScalarCutConnected4 r.tree U K
          (r.embed (p.embed a)) (r.embed (p.embed d)) (r.embed p.mark) r.mark)+
        fullScalarCutGamma T U K a c*(R p r*fullScalarCutConnected4 r.tree U K
          (r.embed (p.embed z)) (r.embed (p.embed d)) (r.embed p.mark) r.mark)+
        fullScalarCutGamma T U K a d*(R p r*fullScalarCutConnected4 r.tree U K
          (r.embed (p.embed z)) (r.embed (p.embed c)) (r.embed p.mark) r.mark)))).sum) := by
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    rw [HI p hp r hr]
  simp only [retainedSignedJets,nativeConnectedHighPairing]
  change ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        (R p r*fullScalarCutMoment r.tree U K (insertedSiteSlots [a,z,c,d] p r)))).sum)).sum/2=_
  rw [HE]
  simp only [mul_add,List.sum_map_add]
  simp_rw [mul_assoc,mul_left_comm _ (nativeLowScalarPairing T U K a z c d),
    mul_left_comm _ (fullScalarCutGamma T U K z d),
    mul_left_comm _ (fullScalarCutGamma T U K z c),
    mul_left_comm _ (fullScalarCutGamma T U K a c),
    mul_left_comm _ (fullScalarCutGamma T U K a d),List.sum_map_mul_left]
  dsimp only [R]
  simp_rw [sum_map_weight_const]
  ring

theorem retained_signed_jets_zero_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (As : List (ℕ→Spin n→Spin n→ℝ)) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (es : List T.Slot) :
    retainedSignedJets n q U b h K As T (fun _=>0) es=0 := by
  simpa only [mul_zero,sub_zero,one_mul,sub_self] using
    retained_signed_jets_sub_smul n q U b h K As T (fun _=>0) (fun _=>0) 1 es

theorem native_retained_high_pairing_zero_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (a c : T.Slot) :
    nativeRetainedHighPairing n q U b h K T (fun _=>0) a c=0 := by
  simp only [nativeRetainedHighPairing,retained_signed_jets_zero_test,mul_zero,sub_zero]

def nativeGPairLowAllocation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed a)) (r.embed p.mark)+
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed a)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed z)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed z)) (r.embed p.mark)))).sum)).sum/2

def nativeLowGammaHighBaseline (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
        (insertedRestTest P (restLowKernel n U b h) p r) []))).sum)).sum/2

theorem native_retained_low_high_eq_G_and_baseline (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    retainedSignedJets n q U b h K [restLowKernel n U b h,restHighKernel n U b h K] T P [a,z]=
      nativeGPairLowAllocation n q U b h K T P a z+
      nativeLowGammaHighBaseline n q U b h K T P a z := by
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
        (insertedRestTest P (restLowKernel n U b h) p r) (insertedSiteSlots [a,z] p r)=
      nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
        (r.embed p.mark) r.mark*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
          (insertedRestTest P (restLowKernel n U b h) p r) []+
      fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed a)) (r.embed p.mark)+
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed a)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed z)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed z)) (r.embed p.mark) := by
    by_cases hcd : r.tree.splitIndex (r.embed p.mark) r.mark < U
    · have haz' : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z)) < U := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,
          (T.markedAttach_embed_preserves 0 p hp).2]
        exact haz
      simpa only [insertedSiteSlots,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using
        native_retained_high_four_eq_scalar_and_G n q U b h K r.tree ho
          (insertedRestTest P (restLowKernel n U b h) p r)
          (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU haz' hcd
    · have H : insertedRestTest P (restLowKernel n U b h) p r=fun _=>0 := by
        funext σ
        simp only [insertedRestTest,restLowKernel,hcd,ite_false,mul_zero]
      rw [H]
      simp only [retained_signed_jets_zero_test,native_retained_high_pairing_zero_test,
        mul_zero,add_zero]
  unfold nativeGPairLowAllocation nativeLowGammaHighBaseline
  change ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
          (insertedRestTest P (restLowKernel n U b h) p r) (insertedSiteSlots [a,z] p r))).sum)).sum/2=_
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
          (insertedRestTest P (restLowKernel n U b h) p r) (insertedSiteSlots [a,z] p r))).sum)=
    (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        (nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z))
          (r.embed p.mark) r.mark*
          retainedSignedJets n q U b h K [restHighKernel n U b h K] r.tree
            (insertedRestTest P (restLowKernel n U b h) p r) []+
        (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed a)) (r.embed p.mark)+
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed a)) r.mark+
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed z)) r.mark+
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U b h) p r) (r.embed (p.embed z)) (r.embed p.mark))))).sum) := by
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    rw [HI p hp r hr]
    ring
  rw [HE]
  simp only [mul_add,List.sum_map_add,add_div]
  ring

def nativeActualMixedScalarBaseline (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  nativeLowGammaHighBaseline n q U b h K T P a z-
    K (T.splitIndex a z)*
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []

theorem actual_first_low_high_centered_eq_G_and_baseline (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 1 0=
      nativeGPairLowAllocation n q U b h K T P a z+
      nativeActualMixedScalarBaseline n q U b h K T P a z := by
  rw [actual_first_low_high_centered_eq_error_first_ledger n q U b h K T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz,
    native_error_first_ledger_eq_centered_high_low n q U b h K T ho P a z,
    ←native_retained_low_high_eq_high_low n q U b h K T ho P [a,z]
      hq0 hq hb hh hK hbm hhm hKm,
    native_retained_low_high_eq_G_and_baseline n q U b h K T ho P a z hU haz]
  unfold nativeActualMixedScalarBaseline
  ring

end OAI.SKFluctuations.Cavity
