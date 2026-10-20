module

public import ComparisonSignedCavityActualOriginalHighExchange

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nativeDummyMonomial_replace_away
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (es : List T.Slot) (hes : ∀a∈es,a≠s)
    (σ : T.withDummy.Assignment) (z : (Spin n×Bool)×Bool) :
    nativeDummyMonomial T (nativeReplaceAtSlot T.withDummy (T.withDummySlot s) σ z) es=
      nativeDummyMonomial T σ es := by
  induction es with
  | nil=>rfl
  | cons a es ih=>
    have ha : T.withDummySlot a≠T.withDummySlot s:=fun H=>
      hes a List.mem_cons_self (T.withDummySlot.injective H)
    have HE:=ih (fun c hc=>hes c (List.mem_cons_of_mem a hc))
    simpa only [nativeDummyMonomial,List.map_cons,slotProduct,nativeReplaceAtSlot_at,
      ite_eq_right ha] using congrArg (fun v=>spinValue (T.withDummy.atSlot σ (T.withDummySlot a)).2*v) HE

theorem native_original_exterior_high_slots_whole_exchange
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (k : ℕ) (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (es : List T.Slot) (hes : ∀a∈es,a≠s) (Q : T.Assignment→(Spin n×Bool)→ℝ) :
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (es.map p.embed)=
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (es.map p.embed) := by
  let QD : T.withDummy.Assignment→((Spin n×Bool)×Bool)→ℝ := fun τ z=>
    Q (T.withDummyPhysical τ) z.1*nativeDummyMonomial T τ es
  have hpD : p.withDummy∈T.withDummy.markedAttach 0 := by
    rw [markedAttach_withDummy]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hhD : k ≤ p.withDummy.tree.splitIndex (p.withDummy.embed (T.withDummySlot s))
      p.withDummy.mark := by
    change k ≤ p.tree.withDummy.splitIndex (p.withDummy.embed (T.withDummySlot s))
      (p.tree.withDummySlot p.mark)
    rw [p.withDummy_embed,p.tree.splitIndex_withDummy]
    exact hh
  have H:=native_target_singleton_whole_profile_exchange T.withDummy (T.withDummySlot s) k
    (native_dummy_singleton T s k h) (nativeDummyWeight_pos n) (nativeDummyFeature n) ho
    p.withDummy hpD hhD (nativeDummyRoot v) (nativeDummyClock q U K)
    (nativeDummyClock_monotone q U K hq hK hKm) (nativeDummyRoot_le_clock_zero v q U K hq0 hK)
    [nativeDummyHighDirection n U b C] QD (nativeDummyField x)
  have HL : (fun σ : p.tree.withDummy.Assignment=>QD (p.withDummy.restrict σ) (p.withDummy.spin σ))=
      (fun σ=>Q (p.restrict (p.tree.withDummyPhysical σ)) (p.spin (p.tree.withDummyPhysical σ))*
        nativeDummyMonomial p.tree σ (es.map p.embed)) := by
    funext σ
    dsimp only [QD]
    rw [p.withDummy_physical_restrict,p.withDummy_physical_spin,nativeDummyMonomial_marked_restrict]
  have HR : (fun σ : p.tree.withDummy.Assignment=>QD
        (nativeReplaceAtSlot T.withDummy (T.withDummySlot s) (p.withDummy.restrict σ) (p.withDummy.spin σ))
        (T.withDummy.atSlot (p.withDummy.restrict σ) (T.withDummySlot s)))=
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict (p.tree.withDummyPhysical σ))
          (p.spin (p.tree.withDummyPhysical σ)))
          (T.atSlot (p.restrict (p.tree.withDummyPhysical σ)) s)*
        nativeDummyMonomial p.tree σ (es.map p.embed)) := by
    funext σ
    dsimp only [QD]
    rw [native_dummy_physical_replace,p.withDummy_physical_restrict,p.withDummy_physical_spin,
      ←T.withDummyPhysical_atSlot,p.withDummy_physical_restrict,
      nativeDummyMonomial_replace_away T s es hes,nativeDummyMonomial_marked_restrict]
  erw [HL,HR] at H
  simp only [List.map_cons,List.map_nil,←nativeDummyLiftKernel_high] at H
  change disorderProfileJets _ _ _ _ _
      ([nativeOriginalHighKernel n U b C].map nativeDummyLiftKernel) p.tree.withDummy _=
    disorderProfileJets _ _ _ _ _
      ([nativeOriginalHighKernel n U b C].map nativeDummyLiftKernel) p.tree.withDummy _ at H
  rw [native_dummy_jets_eq_original_signed n v q x U K _ p.tree ho
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (es.map p.embed),
    native_dummy_jets_eq_original_signed n v q x U K _ p.tree ho
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (es.map p.embed)] at H
  exact H

theorem native_original_exterior_connected_high_whole_exchange
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s a c : T.Slot) (ha : a≠s) (hc : c≠s) (k : ℕ)
    (h : ∀z : T.Slot,k ≤ T.splitIndex s z→z=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (Q : T.Assignment→(Spin n×Bool)→ℝ) :
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (p.embed a) (p.embed c)=
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (p.embed a) (p.embed c) := by
  have H₁:=native_original_exterior_high_slots_whole_exchange n v q x U K b C T ho s k h
    p hp hh hq hq0 hK hKm [a,c] (by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl
      · exact ha
      · exact hc) Q
  have H₀:=native_original_exterior_high_slots_whole_exchange n v q x U K b C T ho s k h
    p hp hh hq hq0 hK hKm [] (by simp) Q
  simp only [List.map_cons,List.map_nil] at H₁ H₀
  unfold nativeOriginalConnectedHighResponse
  rw [H₁,H₀]

end OAI.SKFluctuations.Cavity
