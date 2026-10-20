module

public import ComparisonSignedCavityActualHighPairingMarginal
public import ComparisonSignedCavityActualLongitudinalGhostMarginal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

def nativeGForwardMarkedRow (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) (r.embed p.mark)))).sum)).sum

def nativeGReverseMarkedRow (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) r.mark))).sum)).sum

theorem native_G_forward_marked_row_eq_longitudinal (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU0 : 0 < U) :
    nativeGForwardMarkedRow n q U b h K T P a z=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeRetainedLongitudinalPairing n q U b h K T P a := by
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) (r.embed p.mark)))).sum=
    χ*nativeRetainedHighPairing n q U b h K p.tree (fun σ=>P (p.restRestrict σ)) (p.embed a) p.mark := by
    have HE : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) (r.embed p.mark)))=
      (p.tree.markedAttach 0).map (fun r=>(r.coeff*
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark)*
          nativeRetainedHighPairing n q U b h K p.tree (fun σ=>P (p.restRestrict σ)) (p.embed a) p.mark) := by
      apply List.map_congr_left
      intro r hr
      rw [native_retained_high_pairing_marked_preserves n q U b h K p.tree ho
        (fun σ=>P (p.restRestrict σ)) (p.embed a) p.mark r hr hq0 hq hb hh hK hbm hhm hKm]
      ring
    rw [HE,List.sum_map_mul_right,native_full_gamma_row_hessian n p.tree ho 0 ho U hU0 K]
  unfold nativeGForwardMarkedRow
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) (r.embed p.mark)))).sum)=
    (T.markedAttach 0).map (fun p=>p.coeff*(χ*
      nativeRetainedHighPairing n q U b h K p.tree (fun σ=>P (p.restRestrict σ)) (p.embed a) p.mark)) := by
    apply List.map_congr_left
    intro p hp
    rw [HI p hp]
  rw [HE,sum_map_weight_const]
  rfl

theorem native_G_reverse_marked_row_eq_longitudinal (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU0 : 0 < U) :
    nativeGReverseMarkedRow n q U b h K T P a z=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeRetainedLongitudinalPairing n q U b h K T P a := by
  let L:=nativeRetainedLongitudinalPairing n q U b h K T P a
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) r.mark))).sum=
    fullScalarCutGamma p.tree U K (p.embed z) p.mark*L := by
    have HE : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) r.mark))=
      (p.tree.markedAttach 0).map (fun r=>r.coeff*(fullScalarCutGamma p.tree U K (p.embed z) p.mark*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) r.mark)) := by
      apply List.map_congr_left
      intro r hr
      rw [fullScalarCutGamma_marked_preserves p.tree ho U K (p.embed z) p.mark r hr]
    rw [HE,sum_map_weight_const]
    change fullScalarCutGamma p.tree U K (p.embed z) p.mark*
      nativeRetainedLongitudinalPairing n q U b h K p.tree (fun σ=>P (p.restRestrict σ)) (p.embed a)=_
    rw [native_retained_longitudinal_marked_preserves n q U b h K T ho P a p hp
      hq0 hq hb hh hK hbm hhm hKm hU0]
  unfold nativeGReverseMarkedRow
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) r.mark))).sum)=
    (T.markedAttach 0).map (fun p=>(p.coeff*fullScalarCutGamma p.tree U K (p.embed z) p.mark)*L) := by
    apply List.map_congr_left
    intro p hp
    rw [HI p hp]
    ring
  rw [HE,List.sum_map_mul_right,native_full_gamma_row_hessian n T ho 0 ho U hU0 K]

def nativeFourGMarkedRow (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  nativeGForwardMarkedRow n q U b h K T P a z+
    nativeGReverseMarkedRow n q U b h K T P a z+
    nativeGReverseMarkedRow n q U b h K T P z a+
    nativeGForwardMarkedRow n q U b h K T P z a

theorem native_four_G_marked_row_eq_longitudinal (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (hU0 : 0 < U) :
    nativeFourGMarkedRow n q U b h K T P a z=
      2*(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        (nativeRetainedLongitudinalPairing n q U b h K T P a+
          nativeRetainedLongitudinalPairing n q U b h K T P z) := by
  unfold nativeFourGMarkedRow
  rw [native_G_forward_marked_row_eq_longitudinal n q U b h K T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU0,
    native_G_reverse_marked_row_eq_longitudinal n q U b h K T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU0,
    native_G_reverse_marked_row_eq_longitudinal n q U b h K T ho P z a
      hq0 hq hb hh hK hbm hhm hKm hU0,
    native_G_forward_marked_row_eq_longitudinal n q U b h K T ho P z a
      hq0 hq hb hh hK hbm hhm hKm hU0]
  ring

theorem native_retained_high_pairing_const_mul_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (v : ℝ) :
    nativeRetainedHighPairing n q U b h K T (fun σ=>v*P σ) a c=
      v*nativeRetainedHighPairing n q U b h K T P a c := by
  unfold nativeRetainedHighPairing
  rw [retained_signed_jets_const_mul_test,retained_signed_jets_const_mul_test]
  ring

theorem native_retained_high_pairing_cross_zero (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length)
    (hac : T.splitIndex a c < U) :
    nativeRetainedHighPairing n q U b h K T P a c=0 := by
  rw [←native_connected_high_pairing_eq_retained n q U b h K T ho]
  have HI (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restHighKernel n U b h K) p r) 0*
      fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
        (r.embed p.mark) r.mark=0 := by
    by_cases hef : U ≤ r.tree.splitIndex (r.embed p.mark) r.mark
    · have hac' : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed c)) < U := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
        exact hac
      rw [fullScalarCutConnected4_cross_target_zero r.tree ho U K _ _ _ _ hU hac' hef,mul_zero]
    · have H : insertedRestTest P (restHighKernel n U b h K) p r=fun _=>0 := by
        funext σ
        simp only [insertedRestTest,restHighKernel,lt_of_not_ge hef,ite_true,mul_zero]
      rw [H]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero,zero_mul]
  unfold nativeConnectedHighPairing
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restHighKernel n U b h K) p r) 0*
        fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark)).sum)=(T.markedAttach 0).map (fun _=>0) := by
    apply List.map_congr_left
    intro p hp
    have HR : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restHighKernel n U b h K) p r) 0*
        fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark)=(p.tree.markedAttach 0).map (fun _=>0) := by
      apply List.map_congr_left
      intro r hr
      rw [mul_assoc,HI p hp r hr,mul_zero]
    rw [HR]
    simp only [List.map_const',List.sum_replicate,nsmul_zero,mul_zero]
  rw [HE]
  simp only [List.map_const',List.sum_replicate,nsmul_zero,zero_div]

def nativeGKernelLowAllocation (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (A : ℕ→Spin n→Spin n→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P A p r) (r.embed (p.embed a)) (r.embed p.mark)+
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P A p r) (r.embed (p.embed a)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P A p r) (r.embed (p.embed z)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P A p r) (r.embed (p.embed z)) (r.embed p.mark)))).sum)).sum/2

theorem native_G_Gamma_scalar_low_weight_forward (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z c d : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    (if T.splitIndex c d < U then K (T.splitIndex c d) else 0)*
      (fullScalarCutGamma T U K z d*nativeRetainedHighPairing n q U b h K T P a c)=
      K (T.splitIndex a z)*
        (fullScalarCutGamma T U K z d*nativeRetainedHighPairing n q U b h K T P a c) := by
  by_cases hac : U ≤ T.splitIndex a c
  · by_cases hzd : U ≤ T.splitIndex z d
    · rw [native_cross_split_of_same_cut_blocks T U a z c d haz hac hzd]
      simp only [haz,ite_true]
    · rw [fullScalarCutGamma_cross_zero T ho U K z d hU (lt_of_not_ge hzd)]
      simp only [zero_mul,mul_zero]
  · rw [native_retained_high_pairing_cross_zero n q U b h K T ho P a c hU (lt_of_not_ge hac)]
    simp only [mul_zero]

theorem native_G_Gamma_scalar_low_weight_all (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z c d : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    (if T.splitIndex c d < U then K (T.splitIndex c d) else 0)*
      (fullScalarCutGamma T U K z d*nativeRetainedHighPairing n q U b h K T P a c+
        fullScalarCutGamma T U K z c*nativeRetainedHighPairing n q U b h K T P a d+
        fullScalarCutGamma T U K a c*nativeRetainedHighPairing n q U b h K T P z d+
        fullScalarCutGamma T U K a d*nativeRetainedHighPairing n q U b h K T P z c)=
      K (T.splitIndex a z)*
        (fullScalarCutGamma T U K z d*nativeRetainedHighPairing n q U b h K T P a c+
          fullScalarCutGamma T U K z c*nativeRetainedHighPairing n q U b h K T P a d+
          fullScalarCutGamma T U K a c*nativeRetainedHighPairing n q U b h K T P z d+
          fullScalarCutGamma T U K a d*nativeRetainedHighPairing n q U b h K T P z c) := by
  have haz' : T.splitIndex z a < U:=by rwa [T.splitIndex_symm]
  have H₁:=native_G_Gamma_scalar_low_weight_forward n q U b h K T ho P a z c d hU haz
  have H₂:=native_G_Gamma_scalar_low_weight_forward n q U b h K T ho P a z d c hU haz
  have H₃:=native_G_Gamma_scalar_low_weight_forward n q U b h K T ho P z a d c hU haz'
  have H₄:=native_G_Gamma_scalar_low_weight_forward n q U b h K T ho P z a c d hU haz'
  rw [T.splitIndex_symm d c] at H₂ H₃
  rw [T.splitIndex_symm z a] at H₃ H₄
  linear_combination H₁+H₂+H₃+H₄

theorem native_four_G_marked_row_eq_single_sum (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) :
    nativeFourGMarkedRow n q U b h K T P a z=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*
          (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
              nativeRetainedHighPairing n q U b h K r.tree
                (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) (r.embed p.mark)+
            fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
              nativeRetainedHighPairing n q U b h K r.tree
                (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) r.mark+
            fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
              nativeRetainedHighPairing n q U b h K r.tree
                (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed z)) r.mark+
            fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
              nativeRetainedHighPairing n q U b h K r.tree
                (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed z)) (r.embed p.mark)))).sum)).sum := by
  simp only [nativeFourGMarkedRow,nativeGForwardMarkedRow,nativeGReverseMarkedRow,
    mul_add,List.sum_map_add]

theorem native_G_pure_scalar_low_allocation_eq_longitudinal (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU0 : 0 < U) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeGKernelLowAllocation n q U b h K T P a z (restLowKernel n U 0 K)=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeRetainedLongitudinalPairing n q U b h K T P a+
            nativeRetainedLongitudinalPairing n q U b h K T P z) := by
  let F (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree) : ℝ :=
    fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) (r.embed p.mark)+
      fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed a)) r.mark+
      fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed z)) r.mark+
      fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
        nativeRetainedHighPairing n q U b h K r.tree
          (fun σ=>P (p.restRestrict (r.restRestrict σ))) (r.embed (p.embed z)) (r.embed p.mark)
  have HE (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed a)) (r.embed p.mark)+
        fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed a)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed z)) r.mark+
        fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
          nativeRetainedHighPairing n q U b h K r.tree
            (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed z)) (r.embed p.mark)=
      K (T.splitIndex a z)*F p r := by
    have HA : insertedRestTest P (restLowKernel n U 0 K) p r=
        fun σ=>(if r.tree.splitIndex (r.embed p.mark) r.mark<U then
          K (r.tree.splitIndex (r.embed p.mark) r.mark) else 0)*P (p.restRestrict (r.restRestrict σ)) := by
      funext σ
      simp only [insertedRestTest,restLowKernel,Pi.zero_apply,zero_mul,add_zero]
      split_ifs <;> ring
    rw [HA]
    simp_rw [native_retained_high_pairing_const_mul_test]
    have HS : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
      rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
    have HW:=native_G_Gamma_scalar_low_weight_all n q U b h K r.tree ho
      (fun σ=>P (p.restRestrict (r.restRestrict σ)))
      (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [HS])
    rw [HS] at HW
    dsimp only [F]
    linear_combination HW
  unfold nativeGKernelLowAllocation
  have HL : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed a)) (r.embed p.mark)+
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed a)) r.mark+
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed z)) r.mark+
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed z)) (r.embed p.mark)))).sum)=
      (T.markedAttach 0).map (fun p=>p.coeff*(K (T.splitIndex a z)*
        ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum)) := by
    apply List.map_congr_left
    intro p hp
    have HR : (p.tree.markedAttach 0).map (fun r=>r.coeff*
        (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed a)) (r.embed p.mark)+
          fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed a)) r.mark+
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) (r.embed p.mark)*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed z)) r.mark+
          fullScalarCutGamma r.tree U K (r.embed (p.embed a)) r.mark*
            nativeRetainedHighPairing n q U b h K r.tree
              (insertedRestTest P (restLowKernel n U 0 K) p r) (r.embed (p.embed z)) (r.embed p.mark)))=
        (p.tree.markedAttach 0).map (fun r=>r.coeff*(K (T.splitIndex a z)*F p r)) := by
      apply List.map_congr_left
      intro r hr
      rw [HE p hp r hr]
    rw [HR,sum_map_weight_const]
  rw [HL,sum_map_weight_const]
  change K (T.splitIndex a z)*
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum)).sum/2= _
  have HF:=native_four_G_marked_row_eq_single_sum n q U b h K T P a z
  change nativeFourGMarkedRow n q U b h K T P a z=
    ((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum)).sum at HF
  rw [←HF,native_four_G_marked_row_eq_longitudinal n q U b h K T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU0]
  ring

theorem native_retained_high_pairing_add_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) :
    nativeRetainedHighPairing n q U b h K T (fun σ=>P σ+Q σ) a c=
      nativeRetainedHighPairing n q U b h K T P a c+
        nativeRetainedHighPairing n q U b h K T Q a c := by
  unfold nativeRetainedHighPairing
  rw [retained_signed_jets_add_test,retained_signed_jets_add_test]
  ring

theorem native_G_kernel_low_allocation_add (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (A B : ℕ→Spin n→Spin n→ℝ) :
    nativeGKernelLowAllocation n q U b h K T P a z (fun j σ τ=>A j σ τ+B j σ τ)=
      nativeGKernelLowAllocation n q U b h K T P a z A+
        nativeGKernelLowAllocation n q U b h K T P a z B := by
  have HE (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree) :
      insertedRestTest P (fun j σ τ=>A j σ τ+B j σ τ) p r=
        fun σ=>insertedRestTest P A p r σ+insertedRestTest P B p r σ := by
    funext σ
    dsimp only [insertedRestTest]
    ring
  unfold nativeGKernelLowAllocation
  simp_rw [HE,native_retained_high_pairing_add_test]
  simp only [mul_add,List.sum_map_add]
  ring

theorem native_low_kernel_eq_centered_add_scalar (n U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) :
    restLowKernel n U b h=
      fun j σ τ=>restCenteredLowKernel n U b S j σ τ+restLowKernel n U 0 K j σ τ := by
  funext j σ τ
  dsimp only [restLowKernel,restCenteredLowKernel]
  by_cases hj : j<U
  · simp only [hj,ite_true,Pi.zero_apply,zero_mul,add_zero,hKS]
    ring
  · simp only [hj,ite_false,add_zero]

theorem native_G_low_allocation_eq_longitudinal_add_centered (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU0 : 0 < U) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeGPairLowAllocation n q U b h K T P a z=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeRetainedLongitudinalPairing n q U b h K T P a+
            nativeRetainedLongitudinalPairing n q U b h K T P z)+
        nativeGKernelLowAllocation n q U b h K T P a z (restCenteredLowKernel n U b S) := by
  change nativeGKernelLowAllocation n q U b h K T P a z (restLowKernel n U b h)=_
  rw [native_low_kernel_eq_centered_add_scalar n U b h K S hKS,
    native_G_kernel_low_allocation_add]
  rw [native_G_pure_scalar_low_allocation_eq_longitudinal n q U b h K T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU0 hU haz]
  ring

theorem actual_first_low_high_centered_eq_longitudinal_and_errors (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU0 : 0 < U) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a z) 0 1 1 0=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        K (T.splitIndex a z)*
          (nativeRetainedLongitudinalPairing n q U b h K T P a+
            nativeRetainedLongitudinalPairing n q U b h K T P z)+
        nativeGKernelLowAllocation n q U b h K T P a z (restCenteredLowKernel n U b S)+
        nativeCenteredLowGammaHighLedger n q U b h K S T P a z := by
  rw [actual_first_low_high_centered_eq_G_and_centered_low n q U b h K S hKS T ho P a z
    hq0 hq hb hh hK hbm hhm hKm hU haz,
    native_G_low_allocation_eq_longitudinal_add_centered n q U b h K S hKS T ho P a z
      hq0 hq hb hh hK hbm hhm hKm hU0 hU haz]

end OAI.SKFluctuations.Cavity
