module

public import ComparisonSignedCavityActualOriginalGPairRestoration
public import ComparisonSignedCavityOriginalZeroRestoration

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

 theorem native_original_high_pairing_test_linear (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P Q : T.cavityLeft.Assignment→ℝ)
    (a c : T.Slot) (α β : ℝ) :
    nativeOriginalHighPairing n v q x U K b C T (fun σ=>α*P σ+β*Q σ) a c=
      α*nativeOriginalHighPairing n v q x U K b C T P a c+
      β*nativeOriginalHighPairing n v q x U K b C T Q a c := by
  have HI (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(α*P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))+
          β*Q (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)))*
          nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
            (r.embed p.mark) r.mark σ) x=
      α*r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
          nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
            (r.embed p.mark) r.mark σ) x+
      β*r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
          nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a)) (r.embed (p.embed c))
            (r.embed p.mark) r.mark σ) x := by
    unfold ClockTree.disorderExpect
    simp only [mul_add,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro σ _ <;> ring
  unfold nativeOriginalHighPairing
  simp_rw [HI]
  simp only [mul_add,List.sum_map_add,mul_left_comm,List.sum_map_mul_left]

 theorem native_original_high_pair_restoration_test_linear (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (α β : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalHighPairRestoration n q U b h K C T (fun σ=>α*P σ+β*Q σ) a c=
      α*nativeOriginalHighPairRestoration n q U b h K C T P a c+
      β*nativeOriginalHighPairRestoration n q U b h K C T Q a c := by
  have HP:=native_original_high_pairing_law_restoration n q U b h K C T ho P a c
    hq0 hq hb hh hK hbm hhm hKm
  have HQ:=native_original_high_pairing_law_restoration n q U b h K C T ho Q a c
    hq0 hq hb hh hK hbm hhm hKm
  have HPQ:=native_original_high_pairing_law_restoration n q U b h K C T ho
    (fun σ=>α*P σ+β*Q σ) a c hq0 hq hb hh hK hbm hhm hKm
  have HL:=native_original_high_pairing_test_linear n 0 (cutFullVariance n q U 1 1 b h K) 0
    U K b C T P Q a c α β
  have HZ:=native_original_high_pairing_test_linear n 0 (cutFullVariance n q U 0 0 b h K) 0
    U K b C T P Q a c α β
  change nativeDecoupledOriginalGPairing n q U b h K C T (fun σ=>α*P σ+β*Q σ) a c=
    α*nativeDecoupledOriginalGPairing n q U b h K C T P a c+
      β*nativeDecoupledOriginalGPairing n q U b h K C T Q a c at HZ
  linear_combination -HPQ+α*HP+β*HQ+HL-HZ

 theorem native_original_high_pair_restoration_cross_zero (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hac : T.splitIndex a c<U)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalHighPairRestoration n q U b h K C T P a c=0 := by
  have HP:=native_original_high_pairing_law_restoration n q U b h K C T ho P a c
    hq0 hq hb hh hK hbm hhm hKm
  have HZ:=native_original_high_pairing_cross_zero n 0 (cutFullVariance n q U 0 0 b h K) 0
    U K b C T P a c hac
  change nativeDecoupledOriginalGPairing n q U b h K C T P a c=0 at HZ
  rw [native_original_high_pairing_cross_zero n 0 (cutFullVariance n q U 1 1 b h K) 0
    U K b C T P a c hac,HZ,zero_add] at HP
  exact HP.symm

end OAI.SKFluctuations.Cavity
