module

public import ComparisonSignedCavityActualFullMarkedProfileExchange
public import ComparisonSignedCavityActualOriginalHighMarginal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem native_dummy_physical_replace {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (σ : T.withDummy.Assignment)
    (z : (Spin n×Bool)×Bool) :
    T.withDummyPhysical (nativeReplaceAtSlot T.withDummy (T.withDummySlot s) σ z)=
      nativeReplaceAtSlot T s (T.withDummyPhysical σ) z.1 := by
  classical
  apply T.assignment_ext
  intro c
  rw [T.withDummyPhysical_atSlot,nativeReplaceAtSlot_at,nativeReplaceAtSlot_at]
  by_cases hc : c=s
  · subst c
    simp only [ite_true]
  · have hcD : T.withDummySlot c≠T.withDummySlot s:=fun H=>hc (T.withDummySlot.injective H)
    rw [ite_eq_right hcD,ite_eq_right hc,T.withDummyPhysical_atSlot]

theorem native_dummy_singleton {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (k : ℕ)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s) :
    ∀c : T.withDummy.Slot,k ≤ T.withDummy.splitIndex (T.withDummySlot s) c→c=T.withDummySlot s := by
  intro c hc
  have hd : k ≤ T.splitIndex s (T.withDummySlot.symm c) := by
    have H:=T.splitIndex_withDummy s (T.withDummySlot.symm c)
    rw [Equiv.apply_symm_apply] at H
    rwa [H] at hc
  simpa only [Equiv.apply_symm_apply] using congrArg T.withDummySlot (h _ hd)

theorem native_original_high_pair_slots_whole_exchange
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (k : ℕ) (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→ℝ) (pair : Bool) :
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (if pair then [p.embed s,p.mark] else [])=
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (if pair then [p.embed s,p.mark] else []) := by
  let QD : T.withDummy.Assignment→((Spin n×Bool)×Bool)→ℝ := fun τ z=>
    Q (T.withDummyPhysical τ) z.1*
      (if pair then spinValue (T.withDummy.atSlot τ (T.withDummySlot s)).2*spinValue z.2 else 1)
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
        nativeDummyMonomial p.tree σ (if pair then [p.embed s,p.mark] else [])) := by
    funext σ
    dsimp only [QD]
    rw [p.withDummy_physical_restrict,p.withDummy_physical_spin]
    cases pair with
    | false=>simp only [Bool.false_eq_true,ite_false,nativeDummyMonomial,List.map_nil,slotProduct]
    | true=>
      simp only [ite_true]
      rw [p.withDummy.restrict_at,p.withDummy_embed,p.withDummy.spin_at]
      simp only [nativeDummyMonomial,List.map_cons,List.map_nil,slotProduct,mul_one]
      rfl
  have HR : (fun σ : p.tree.withDummy.Assignment=>QD
        (nativeReplaceAtSlot T.withDummy (T.withDummySlot s) (p.withDummy.restrict σ) (p.withDummy.spin σ))
        (T.withDummy.atSlot (p.withDummy.restrict σ) (T.withDummySlot s)))=
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict (p.tree.withDummyPhysical σ))
          (p.spin (p.tree.withDummyPhysical σ)))
          (T.atSlot (p.restrict (p.tree.withDummyPhysical σ)) s)*
        nativeDummyMonomial p.tree σ (if pair then [p.embed s,p.mark] else [])) := by
    funext σ
    dsimp only [QD]
    rw [native_dummy_physical_replace,p.withDummy_physical_restrict,p.withDummy_physical_spin,
      ←T.withDummyPhysical_atSlot,p.withDummy_physical_restrict]
    cases pair with
    | false=>simp only [Bool.false_eq_true,ite_false,nativeDummyMonomial,List.map_nil,slotProduct]
    | true=>
      simp only [ite_true,nativeReplaceAtSlot_at]
      rw [p.withDummy.spin_at,p.withDummy.restrict_at,p.withDummy_embed]
      simp only [nativeDummyMonomial,List.map_cons,List.map_nil,slotProduct,mul_one]
      dsimp only [MarkedPlacement.withDummy]
      ring
  erw [HL,HR] at H
  simp only [List.map_cons,List.map_nil,←nativeDummyLiftKernel_high] at H
  change disorderProfileJets _ _ _ _ _
      ([nativeOriginalHighKernel n U b C].map nativeDummyLiftKernel) p.tree.withDummy _=
    disorderProfileJets _ _ _ _ _
      ([nativeOriginalHighKernel n U b C].map nativeDummyLiftKernel) p.tree.withDummy _ at H
  rw [native_dummy_jets_eq_original_signed n v q x U K _ p.tree ho
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (if pair then [p.embed s,p.mark] else []),
    native_dummy_jets_eq_original_signed n v q x U K _ p.tree ho
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (if pair then [p.embed s,p.mark] else [])] at H
  exact H

theorem native_original_connected_high_whole_exchange
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (k : ℕ) (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (Q : T.Assignment→(Spin n×Bool)→ℝ) :
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (p.embed s) p.mark=
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (p.embed s) p.mark := by
  have H₁:=native_original_high_pair_slots_whole_exchange n v q x U K b C T ho s k h p hp hh
    hq hq0 hK hKm Q true
  have H₀:=native_original_high_pair_slots_whole_exchange n v q x U K b C T ho s k h p hp hh
    hq hq0 hK hKm Q false
  simp only [ite_true,Bool.false_eq_true,ite_false] at H₁ H₀
  unfold nativeOriginalConnectedHighResponse
  rw [H₁,H₀]

end OAI.SKFluctuations.Cavity
