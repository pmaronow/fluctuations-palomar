module

public import ComparisonSignedCavityStarFieldTestFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]

theorem native_target_singleton_full_rest_star_field_exchange
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ)
    (h : NativeTargetStarSingleton T s star)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (hh : star<p.tree.splitIndex (p.embed s) p.mark)
    (q : ℕ → ι → ℝ≥0) (Q : (ι→ℝ) → T.cavityLeft.Assignment → S → ℝ) (x : ι → ℝ) :
    nativeStarFieldTestMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star q
      (fun y σ=>Q y (p.restRestrict σ) (p.restSpin σ)) x=
    nativeStarFieldTestMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star q (fun y σ=>Q y
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) (p.restSpin σ))
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s))) x := by
  induction T generalizing a star q x with
  | leaf=>
    have HL:=p.tree.splitIndex_le_clockLength (p.embed s) p.mark
    simp only [List.length_nil] at HL
    omega
  | @step b tail T ih=>
    cases star with
    | zero=>
      rw [nativeStarFieldTestMean_zero,nativeStarFieldTestMean_zero]
      exact native_target_singleton_full_rest_exchange (T.step b) s 1
        (fun c hc=>h c (by omega)) hw φ ho p hp (by omega) q
        (Q x) x
    | succ star=>
      rcases List.mem_cons.mp hp with rfl | hp
      · change star+1<0 at hh
        omega
      · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
        have hi : NativeTargetStarSingleton T s star := by
          intro c hc
          exact h c (by change star+1<1+T.splitIndex s c;omega)
        have hh' : star<r.tree.splitIndex (r.embed s) r.mark := by
          change star+1<1+r.tree.splitIndex (r.embed s) r.mark at hh
          omega
        change shiftedMean _ _ _
          (nativeStarFieldTestMean w φ r.tree.cavityLeft
            (r.tree.cavityLeftSlot (r.embed s)) star (fun j=>q (j+1))
            (fun y σ=>Q y (r.restRestrict σ) (r.restSpin σ))) x=
          shiftedMean _ _ _ (nativeStarFieldTestMean w φ r.tree.cavityLeft
            (r.tree.cavityLeftSlot (r.embed s)) star (fun j=>q (j+1)) (fun y σ=>Q y
              (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (r.restRestrict σ) (r.restSpin σ))
              (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot s)))) x
        congr 1
        funext y
        exact ih s star hi ho.2.2 r hr hh' (fun j=>q (j+1)) Q y
  | @fork tail T V ihT ihV=>
    cases star with
    | zero=>
      rw [nativeStarFieldTestMean_zero,nativeStarFieldTestMean_zero]
      exact native_target_singleton_full_rest_exchange (T.fork V) s 1
        (fun c hc=>h c (by omega)) hw φ ho p hp (by omega) q
        (Q x) x
    | succ star=>
      rcases List.mem_cons.mp hp with rfl | hp
      · change star+1<0 at hh
        omega
      · rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
          cases s with
          | inr s=>change star+1<0 at hh;omega
          | inl s=>
            have hi : NativeTargetStarSingleton T s (star+1) := by
              intro c hc
              exact Sum.inl.inj (h (Sum.inl c) hc)
            have hh' : star+1<r.tree.splitIndex (r.embed s) r.mark:=hh
            simp_rw [MarkedPlacement.restRestrict_left,MarkedPlacement.restSpin_left]
            change (∑τ,V.cavityLeft.weight w φ q τ x*
              nativeStarFieldTestMean w φ r.tree.cavityLeft
                (r.tree.cavityLeftSlot (r.embed s)) (star+1) q
                (fun y σ=>Q y (r.restRestrict σ,τ) (r.restSpin σ)) x)=
              (∑τ,V.cavityLeft.weight w φ q τ x*
                nativeStarFieldTestMean w φ r.tree.cavityLeft
                  (r.tree.cavityLeftSlot (r.embed s)) (star+1) q (fun y σ=>Q y
                    (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
                      (r.restRestrict σ) (r.restSpin σ),τ)
                    (T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot s))) x)
            apply Finset.sum_congr rfl
            intro τ _
            congr 1
            exact ihT s (star+1) hi ho r hr hh' q (fun y σ u=>Q y (σ,τ) u) x
        · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
          cases s with
          | inl s=>change star+1<0 at hh;omega
          | inr s=>
            have hi : NativeTargetStarSingleton V s (star+1) := by
              intro c hc
              exact Sum.inr.inj (h (Sum.inr c) hc)
            have hh' : star+1<r.tree.splitIndex (r.embed s) r.mark:=hh
            simp_rw [MarkedPlacement.restRestrict_right,MarkedPlacement.restSpin_right]
            change (∑τ,T.cavityLeft.weight w φ q τ x*
              nativeStarFieldTestMean w φ r.tree.cavityLeft
                (r.tree.cavityLeftSlot (r.embed s)) (star+1) q
                (fun y σ=>Q y (τ,r.restRestrict σ) (r.restSpin σ)) x)=
              (∑τ,T.cavityLeft.weight w φ q τ x*
                nativeStarFieldTestMean w φ r.tree.cavityLeft
                  (r.tree.cavityLeftSlot (r.embed s)) (star+1) q (fun y σ=>Q y
                    (τ,nativeReplaceAtSlot V.cavityLeft (V.cavityLeftSlot s)
                      (r.restRestrict σ) (r.restSpin σ))
                    (V.cavityLeft.atSlot (r.restRestrict σ) (V.cavityLeftSlot s))) x)
            apply Finset.sum_congr rfl
            intro τ _
            congr 1
            exact ihV s (star+1) hi ho r hr hh' q (fun y σ u=>Q y (τ,σ) u) x

end OAI.SKFluctuations.Hierarchy.ClockTree
