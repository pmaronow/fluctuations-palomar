module

public import ComparisonSignedCavityActualAllocatedEndpoint
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

theorem fullScalarCutConnected4_actual_block_support {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a c e f : T.Slot) (hU : U ≤ as.length)
    (hef : U ≤ T.splitIndex e f) :
    fullScalarCutConnected4 T U K a c e f=
      if U≤T.splitIndex a c ∧ U≤T.splitIndex a e ∧ U≤T.splitIndex a f ∧ e≠f
      then fullScalarCutConnected4 T U K a c e f else 0 := by
  by_cases hac : U ≤ T.splitIndex a c
  · by_cases hae : U ≤ T.splitIndex a e
    · have haf : U ≤ T.splitIndex a f:=T.splitIndex_cut_trans U a e f hae hef
      by_cases hdiag : e=f
      · subst f
        rw [fullScalarCutConnected4_high_self_zero T ho U K]
        simp
      · rw [ite_eq_left ⟨hac,hae,haf,hdiag⟩]
    · have Hne : T.cutBlock U hU a ≠ T.cutBlock U hU e := by
        intro H
        exact hae ((T.cutBlock_eq_iff U hU a e).mp H)
      have hca : T.cutBlock U hU c=T.cutBlock U hU a:=
        ((T.cutBlock_eq_iff U hU a c).mpr hac).symm
      have hfe : T.cutBlock U hU f=T.cutBlock U hU e:=
        ((T.cutBlock_eq_iff U hU e f).mpr hef).symm
      have hcross : ∀s∈[a,c],∀t∈[e,f],T.splitIndex s t < U:=
        cut_block_cross_list T U hU [a,c] [e,f] (T.cutBlock U hU a) (T.cutBlock U hU e)
          (by intro s hs;simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
              rcases hs with rfl | rfl <;> first | rfl | exact hca)
          (by intro t ht;simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
              rcases ht with rfl | rfl <;> first | rfl | exact hfe) Hne
      rw [fullScalarCutConnected4_separate_pairs_zero T ho U (by omega) hU K a c e f hcross]
      simp
  · rw [fullScalarCutConnected4_cross_target_zero T ho U K a c e f hU (lt_of_not_ge hac) hef]
    simp

theorem native_original_high_G_atom_eq_unmasked_rest_kernel {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (b h K C : ℕ→ℝ) (hKC : ∀ j,K j=h j+b j*C j)
    (a c e f : T.Slot) (hU : U ≤ as.length) (σ : T.Assignment) :
    nativeOriginalHighGAtom T U K b C a c e f σ=
      (1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*
        restHighKernel n U b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1 := by
  by_cases hef : U ≤ T.splitIndex e f
  · have Hsupport:=fullScalarCutConnected4_actual_block_support T ho U K a c e f hU hef
    unfold nativeOriginalHighGAtom restHighKernel
    simp only [not_lt.mpr hef,ite_false,hKC]
    rw [Hsupport]
    split_ifs
    · simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]
      ring
    · simp only [mul_zero,zero_mul]
  · have hnot : ¬(U≤T.splitIndex a c ∧ U≤T.splitIndex a e ∧ U≤T.splitIndex a f ∧ e≠f) := by
      intro H
      apply hef
      exact T.splitIndex_cut_trans U e a f (by simpa only [T.splitIndex_symm] using H.2.1) H.2.2.1
    simp only [nativeOriginalHighGAtom,hnot,ite_false,restHighKernel,lt_of_not_ge hef,
      ite_true,mul_zero]

def nativeDecoupledOriginalGPairing (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      r.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
        (fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
          nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
            (r.embed p.mark) r.mark σ) 0)).sum)).sum

theorem native_decoupled_original_G_placement_eq_retained (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree) :
    r.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
      (fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
        nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark σ) 0=
      (r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (insertedRestTest P (restHighKernel n U b h K) p r) 0*
        fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark)/2 := by
  let A:=(1/2:ℝ)*fullScalarCutConnected4 r.tree U K (r.embed (p.embed a)) (r.embed (p.embed c))
    (r.embed p.mark) r.mark
  have Htest : (fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
      nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
        (r.embed p.mark) r.mark σ)=
    (fun σ=>A*insertedRestTest P (restHighKernel n U b h K) p r (r.tree.cavityAssignment σ).1) := by
    funext σ
    rw [native_original_high_G_atom_eq_unmasked_rest_kernel r.tree ho U b h K C hKC
      (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark hU]
    dsimp only [A,insertedRestTest,ClockTree.MarkedPlacement.restSpin]
    rw [r.restRestrict_at,r.tree.atSlot_cavityLeft,r.tree.atSlot_cavityLeft]
    ring
  rw [Htest,r.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho,
    native_decoupled_rest_expect n q U b h K r.tree ho]
  dsimp only [A]
  ring

theorem native_retained_high_pairing_eq_decoupled_original_G (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length) :
    nativeRetainedHighPairing n q U b h K T P a c=
      nativeDecoupledOriginalGPairing n q U b h K C T P a c := by
  rw [←native_connected_high_pairing_eq_retained n q U b h K T ho]
  unfold nativeDecoupledOriginalGPairing
  simp_rw [native_decoupled_original_G_placement_eq_retained n q U b h K C hKC T ho P a c hU]
  unfold nativeConnectedHighPairing
  simp only [div_eq_mul_inv,←mul_assoc,List.sum_map_mul_right]

def nativeOriginalLongitudinalPairing (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ) (a : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      ((r.tree.markedAttach 0).map (fun z=>z.coeff*
        z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*
            nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
              (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x)).sum)).sum)).sum

theorem native_retained_longitudinal_eq_decoupled_original_L (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) (hU : U ≤ as.length) :
    nativeRetainedLongitudinalPairing n q U b h K T P a=
      nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 0 0 b h K) 0 U K b C T
        (fun σ=>P (T.cavityAssignment σ).1) a := by
  unfold nativeRetainedLongitudinalPairing nativeOriginalLongitudinalPairing
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [native_retained_high_pairing_eq_decoupled_original_G n q U b h K C hKC p.tree ho
    (fun σ=>P (p.restRestrict σ)) (p.embed a) p.mark hU]
  unfold nativeDecoupledOriginalGPairing
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  congr 1
  congr 1
  funext σ
  dsimp only
  rw [p.restRestrict_actual,r.restRestrict_actual,z.restRestrict_actual]

private theorem original_full_expect_sub_smul (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (P Q : T.Assignment→ℝ) (c : ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>P σ-c*Q σ) x=
      T.disorderExpect (fullWeight n) (fullFeature n) v q P x-
      c*T.disorderExpect (fullWeight n) (fullFeature n) v q Q x := by
  unfold ClockTree.disorderExpect
  simp only [mul_sub,Finset.sum_sub_distrib]
  have H : (∑σ,T.disorderWeight (fullWeight n) (fullFeature n) v q σ x*(c*Q σ))=
      c*(∑σ,T.disorderWeight (fullWeight n) (fullFeature n) v q σ x*Q σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  rw [H]

theorem native_original_longitudinal_sub_smul (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ) (a : T.Slot) (c : ℝ) :
    nativeOriginalLongitudinalPairing n v q x U K b C T (fun σ=>P σ-c*Q σ) a=
      nativeOriginalLongitudinalPairing n v q x U K b C T P a-
      c*nativeOriginalLongitudinalPairing n v q x U K b C T Q a := by
  have HI (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
      (z : ClockTree.MarkedPlacement r.tree) :
    z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(P (p.restrict (r.restrict (z.restrict σ)))-c*Q (p.restrict (r.restrict (z.restrict σ))))*
        nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x=
    z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*
        nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x-
    c*z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>Q (p.restrict (r.restrict (z.restrict σ)))*
        nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x := by
    have Htest : (fun σ=>(P (p.restrict (r.restrict (z.restrict σ)))-c*Q (p.restrict (r.restrict (z.restrict σ))))*
        nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ)=
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*
        nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ-
        c*(Q (p.restrict (r.restrict (z.restrict σ)))*
          nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
            (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ)) := by funext σ;ring
    rw [Htest,original_full_expect_sub_smul]
  unfold nativeOriginalLongitudinalPairing
  simp only [HI,mul_sub,sum_map_sub_explicit]
  simp_rw [sum_map_weight_const]

theorem native_original_longitudinal_centering (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ) (a : T.Slot) :
    let mean:=T.disorderExpect (fullWeight n) (fullFeature n) v q P x
    nativeOriginalLongitudinalPairing n v q x U K b C T (fun σ=>P σ-mean) a=
      nativeOriginalLongitudinalPairing n v q x U K b C T P a-
      mean*nativeOriginalLongitudinalPairing n v q x U K b C T (fun _=>1) a := by
  simpa only [mul_one] using native_original_longitudinal_sub_smul n v q x U K b C T P (fun _=>1) a
    (T.disorderExpect (fullWeight n) (fullFeature n) v q P x)

end OAI.SKFluctuations.Cavity
