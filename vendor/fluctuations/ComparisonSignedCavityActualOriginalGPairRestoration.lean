module

public import ComparisonSignedCavityActualAuxiliaryGammaTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
attribute [local instance] Classical.propDecidable

def nativeOriginalHighPairing (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
          nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
            (r.embed p.mark) r.mark σ) x)).sum)).sum

def nativeOriginalHighPairRestoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      nativeActualLawRestorationRemainder n q U b h K r.tree
        (fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
          nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
            (r.embed p.mark) r.mark σ))).sum)).sum

theorem native_original_high_pairing_law_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalHighPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b C T P a c=
      nativeDecoupledOriginalGPairing n q U b h K C T P a c+
      nativeOriginalHighPairRestoration n q U b h K C T P a c := by
  unfold nativeOriginalHighPairing nativeDecoupledOriginalGPairing nativeOriginalHighPairRestoration
  simp_rw [actual_original_law_eq_decoupled_add_restoration n q U b h K _ ho _
    hq0 hq hb hh hK hbm hhm hKm]
  simp only [mul_add,List.sum_map_add]

theorem native_original_high_pairing_eq_retained_add_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalHighPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b C T P a c=
      nativeRetainedHighPairing n q U b h K T P a c+
      nativeOriginalHighPairRestoration n q U b h K C T P a c := by
  rw [native_original_high_pairing_law_restoration n q U b h K C T ho P a c
    hq0 hq hb hh hK hbm hhm hKm,
    ←native_retained_high_pairing_eq_decoupled_original_G n q U b h K C hKC T ho P a c hU]

theorem native_original_high_pairing_cross_zero (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ)
    (a c : T.Slot) (hac : T.splitIndex a c < U) :
    nativeOriginalHighPairing n v q x U K b C T P a c=0 := by
  have Htest (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      (fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
        nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark σ)=fun _=>0 := by
    funext σ
    have Hsplit : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed c))=T.splitIndex a c := by
      rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
    simp only [nativeOriginalHighGAtom,Hsplit,not_le.mpr hac,false_and,ite_false,mul_zero]
  unfold nativeOriginalHighPairing
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hy
  rw [mul_eq_zero]
  right
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hz
  rw [Htest p hp r hr]
  simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]

theorem native_original_G_Gamma_centered_low_test_eq_target_split (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (b K S : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (σc σd : T.cavityLeft.Assignment→Spin n)
    (a z c d : T.Slot) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    fullScalarCutGamma T U K z d*
      nativeOriginalHighPairing n v q x U K b S T
        (fun σ=>P σ*restCenteredLowKernel n U b S (T.splitIndex c d) (σc σ) (σd σ)) a c=
    fullScalarCutGamma T U K z d*
      nativeOriginalHighPairing n v q x U K b S T
        (fun σ=>P σ*restCenteredFixedForkKernel n b S (T.splitIndex a z)
          (T.splitIndex c d) (σc σ) (σd σ)) a c := by
  by_cases hac : U ≤ T.splitIndex a c
  · by_cases hzd : U ≤ T.splitIndex z d
    · rw [native_cross_split_of_same_cut_blocks T U a z c d haz hac hzd]
      simp only [restCenteredLowKernel,haz,ite_true,restCenteredFixedForkKernel]
    · rw [fullScalarCutGamma_cross_zero T ho U K z d hU (lt_of_not_ge hzd)]
      simp only [zero_mul]
  · rw [native_original_high_pairing_cross_zero n v q x U K b S T _ a c (lt_of_not_ge hac),
      native_original_high_pairing_cross_zero n v q x U K b S T _ a c (lt_of_not_ge hac)]

end OAI.SKFluctuations.Cavity
