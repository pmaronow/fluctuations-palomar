module

public import ComparisonSignedCavitySixBlockAllocation
public import ComparisonSignedCavityObservedGammaCollapse
public import ComparisonSignedCavityMeanCancellation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000

theorem retained_signed_jets_sub_smul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (As : List (ℕ→Spin n→Spin n→ℝ)) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as)
    (P Q : T.cavityLeft.Assignment→ℝ) (c : ℝ) (es : List T.Slot) :
    retainedSignedJets n q U b h K As T (fun σ=>P σ-c*Q σ) es=
      retainedSignedJets n q U b h K As T P es-c*retainedSignedJets n q U b h K As T Q es := by
  induction As generalizing T P Q es with
  | nil =>
    simp only [retainedSignedJets,ClockTree.disorderExpect,mul_sub,Finset.sum_sub_distrib]
    have H : (∑σ,ClockTree.disorderWeight (restWeight n) (restFeature n) T.cavityLeft 0 q σ 0*(c*Q σ))=
        c*(∑σ,ClockTree.disorderWeight (restWeight n) (restFeature n) T.cavityLeft 0 q σ 0*Q σ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    rw [H]
    ring
  | cons A As ih =>
    have H (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree) :
        insertedRestTest (fun σ=>P σ-c*Q σ) A p r=
          (fun σ=>insertedRestTest P A p r σ-c*insertedRestTest Q A p r σ) := by
      funext σ
      unfold insertedRestTest
      ring
    simp only [retainedSignedJets,H,ih]
    rw [native_signed_double_sum_sub]
    ring

def nativeRetainedHighPairing (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  retainedSignedJets n q U b h K [restHighKernel n U b h K] T P [a,c]-
    fullScalarCutGamma T U K a c*
      retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []

def nativeConnectedHighPairing (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest P (restHighKernel n U b h K) p r) 0*
      fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
        (r.embed p.mark) r.mark)).sum)).sum/2

theorem native_connected_high_pairing_eq_retained
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) :
    nativeConnectedHighPairing n q U b h K T P a c=
      nativeRetainedHighPairing n q U b h K T P a c := by
  let F := fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restHighKernel n U b h K) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [a,c] p r)
  let G := fun (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)=>
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restHighKernel n U b h K) p r) 0*
        fullScalarCutMoment r.tree U K (insertedSiteSlots [] p r)
  have HE : (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*
        r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (insertedRestTest P (restHighKernel n U b h K) p r) 0*
        fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark)).sum)=
    (T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun r=>r.coeff*(F p r-fullScalarCutGamma T U K a c*G p r))).sum) := by
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    unfold fullScalarCutConnected4
    rw [fullScalarCutGamma_double_preserves T ho U K a c p hp r hr]
    simp only [F,G,insertedSiteSlots,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      fullScalarCutGamma]
    ring
  unfold nativeConnectedHighPairing
  rw [HE,native_signed_double_sum_sub]
  simp only [nativeRetainedHighPairing,retainedSignedJets,F,G]
  ring

theorem native_retained_high_pairing_eq_centered_coefficient
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) :
    nativeRetainedHighPairing n q U b h K T P a c=
      nativeRetainedCenteredCoefficient n q U b h K T P [a,c] 0 1 := by
  simp only [nativeRetainedCenteredCoefficient,productJet3,Fin.val_zero,List.replicate_zero,
    List.replicate_one,List.nil_append,retainedSignedJets]
  rw [T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho]
  simp only [one_mul]
  rfl

theorem actual_frozen_high_pairing_eq_retained
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    cutFrozenCenteredJet n q U b h K T P (sitePair T a c) 0 0 1 0=
      nativeRetainedHighPairing n q U b h K T P a c := by
  rw [←nativeScalarTest_pair,actual_frozen_centered_coefficient_eq_native_retained n q U b h K
    T ho P [a,c] hq0 hq hb hh hK hbm hhm hKm,
    ←native_retained_high_pairing_eq_centered_coefficient n q U b h K T ho]

theorem native_retained_high_pairing_sub_smul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P Q : T.cavityLeft.Assignment→ℝ) (r : ℝ) (a c : T.Slot) :
    nativeRetainedHighPairing n q U b h K T (fun σ=>P σ-r*Q σ) a c=
      nativeRetainedHighPairing n q U b h K T P a c-
        r*nativeRetainedHighPairing n q U b h K T Q a c := by
  unfold nativeRetainedHighPairing
  simp only [retained_signed_jets_sub_smul]
  ring

theorem native_retained_high_pairing_target_self_zero
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) :
    nativeRetainedHighPairing n q U b h K T P a a=0 := by
  rw [←native_connected_high_pairing_eq_retained n q U b h K T ho]
  simp only [nativeConnectedHighPairing,fullScalarCutConnected4_target_self_zero _ ho,
    mul_zero,List.map_const',List.sum_replicate,nsmul_zero,zero_div]

theorem fullScalarCutConnected4_high_self_zero
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ) (a c e : T.Slot) :
    fullScalarCutConnected4 T U K a c e e=0 := by
  have H : fullScalarCutMoment T U K [a,c,e,e]=fullScalarCutMoment T U K [e,e,a,c] := by
    unfold fullScalarCutMoment scalarCutMoment
    congr 1
    funext σ
    simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
    ring
  unfold fullScalarCutConnected4
  rw [H,fullScalarCutMoment_cancel_pair,fullScalarCutGamma_self T ho U K]
  change fullScalarCutGamma T U K a c-fullScalarCutGamma T U K a c*1=0
  ring

theorem native_connected_high_placement_diagonal_zero
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (hdiag : r.embed p.mark=r.mark) :
    r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (insertedRestTest P (restHighKernel n U b h K) p r) 0*
      fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
        (r.embed p.mark) r.mark=0 := by
  rw [←hdiag,fullScalarCutConnected4_high_self_zero r.tree ho,mul_zero]

def nativeRetainedLongitudinalPairing (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    nativeRetainedHighPairing n q U b h K p.tree
      (fun σ=>P (p.restRestrict σ)) (p.embed a) p.mark)).sum

theorem native_retained_longitudinal_sub_smul
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P Q : T.cavityLeft.Assignment→ℝ) (r : ℝ) (a : T.Slot) :
    nativeRetainedLongitudinalPairing n q U b h K T (fun σ=>P σ-r*Q σ) a=
      nativeRetainedLongitudinalPairing n q U b h K T P a-
        r*nativeRetainedLongitudinalPairing n q U b h K T Q a := by
  unfold nativeRetainedLongitudinalPairing
  simp only [native_retained_high_pairing_sub_smul,mul_sub]
  rw [sum_map_sub_explicit,←List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  ring

theorem native_retained_longitudinal_centered_test
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) :
    let mean := T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0
    nativeRetainedLongitudinalPairing n q U b h K T (fun σ=>P σ-mean) a=
      nativeRetainedLongitudinalPairing n q U b h K T P a-
        mean*nativeRetainedLongitudinalPairing n q U b h K T (fun _=>1) a := by
  simpa only [mul_one] using native_retained_longitudinal_sub_smul n q U b h K T P (fun _=>1)
    (T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0) a

theorem native_retained_longitudinal_pair_centering
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (chi Kstar mean : ℝ) :
    chi*Kstar*(nativeRetainedLongitudinalPairing n q U b h K T (fun σ=>P σ-mean) a+
      nativeRetainedLongitudinalPairing n q U b h K T (fun σ=>P σ-mean) z)=
    chi*Kstar*(nativeRetainedLongitudinalPairing n q U b h K T P a+
      nativeRetainedLongitudinalPairing n q U b h K T P z)-
    chi*Kstar*mean*(nativeRetainedLongitudinalPairing n q U b h K T (fun _=>1) a+
      nativeRetainedLongitudinalPairing n q U b h K T (fun _=>1) z) := by
  have Ha := native_retained_longitudinal_sub_smul n q U b h K T P (fun _=>1) mean a
  have Hz := native_retained_longitudinal_sub_smul n q U b h K T P (fun _=>1) mean z
  simp only [mul_one] at Ha Hz
  rw [Ha,Hz]
  ring

end OAI.SKFluctuations.Cavity
