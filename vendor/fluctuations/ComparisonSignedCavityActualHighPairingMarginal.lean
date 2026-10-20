module

public import ComparisonSignedCavityActualLowSplitSupport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000

theorem native_retained_high_marked_slots_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
      (fun σ=>P (p.restRestrict σ)) (es.map p.embed)=
    retainedSignedJets n q U b h K [restHighKernel n U b h K] T P es := by
  classical
  let D:=cutTSlope n U 0 b h K
  let B : ℝ:=∑ j : Fin (as.length+1),∑ i : FullCoordinate n,|D j.val i|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hD : ∀ A∈[D],∀ j,j ≤ as.length → ∀ i,|A j i| ≤ B := by
    intro A hA j hj i
    simp only [List.mem_singleton] at hA
    subst A
    let r : Fin (as.length+1):=⟨j,by omega⟩
    have H₁ : |D j i| ≤ ∑ z : FullCoordinate n,|D j z| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun z : FullCoordinate n=>|D j z|)
        (fun _ _=>abs_nonneg _) (Finset.mem_univ i)
    have H₂ : (∑ z : FullCoordinate n,|D j z|) ≤ B := by
      simpa only [B,r] using (Finset.single_le_sum
        (s:=Finset.univ) (f:=fun t : Fin (as.length+1)=>∑ z : FullCoordinate n,|D t.val z|)
        (fun _ _=>Finset.sum_nonneg fun _ _=>abs_nonneg _) (Finset.mem_univ r))
    exact H₁.trans H₂
  have HQ : ∀ i,Monotone (fun j=>cutFullVariance n q U 0 0 b h K j i) :=
    cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm
  have HQ0 : ∀ i,(0 : FullCoordinate n→ℝ) i ≤ cutFullVariance n q U 0 0 b h K 0 i :=
    fun i=>cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0 i
  have H : ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0 ([D].map (ReplicaTree.coordinateProfile (fullFeature n)))
      p.tree (fun σ=>P (T.cavityAssignment (p.restrict σ)).1*siteMonomial T (p.restrict σ) es)=
    ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) 0 ([D].map (ReplicaTree.coordinateProfile (fullFeature n)))
      T (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es) := by
    rw [ClockTree.disorderProfileJets_eq_clipDirections (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 0 b h K) 0 [D] p.tree _,
      ClockTree.disorderProfileJets_eq_clipDirections (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 0 b h K) 0 [D] T _]
    exact T.markedAttach_profileJets_preserves_actual (fullWeight_pos n) (fullFeature n) ho p hp
      0 (cutFullVariance n q U 0 0 b h K) HQ HQ0 ([D].map (ClockTree.clipDirection as.length))
      hB (ClockTree.clipDirection_bounded as.length [D] hB hD) (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es) 0
  rw [←actual_site_rest_jets_eq_retained n q U b h K [restHighKernel n U b h K]
      p.tree ho (fun σ=>P (p.restRestrict σ)) (es.map p.embed),
    ←actual_site_rest_jets_eq_retained n q U b h K [restHighKernel n U b h K] T ho P es]
  simpa only [List.map_cons,List.map_nil,siteRestKernel_eq_cut_high,siteMonomial_marked_restrict,
    p.restRestrict_actual,D] using H

theorem native_retained_high_pairing_marked_preserves (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeRetainedHighPairing n q U b h K p.tree (fun σ=>P (p.restRestrict σ)) (p.embed a) (p.embed c)=
      nativeRetainedHighPairing n q U b h K T P a c := by
  unfold nativeRetainedHighPairing
  have H:=native_retained_high_marked_slots_preserves n q U b h K T ho P [a,c] p hp
    hq0 hq hb hh hK hbm hhm hKm
  simp only [List.map_cons,List.map_nil] at H
  rw [H,native_retained_high_marked_preserves n q U b h K T ho P p hp
      hq0 hq hb hh hK hbm hhm hKm,
    fullScalarCutGamma_marked_preserves T ho U K a c p hp]

end OAI.SKFluctuations.Cavity
