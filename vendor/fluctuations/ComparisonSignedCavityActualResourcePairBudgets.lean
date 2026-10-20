module

public import ComparisonSignedCavityActualInitialPairMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
variable {as : List PositiveMass}

omit [Fintype S] [Nonempty S] in
theorem native_frozen_tags_length_le {i star : ℕ}
    (Fs : List (NativeFrozenResource S as i star))
    (F : NativeFrozenResource S as i star) (hF : F∈Fs) :
    F.monomial.tags.length≤(Fs.flatMap (fun G=>G.monomial.tags)).length := by
  induction Fs with
  | nil=>cases hF
  | cons G Fs ih=>
    rcases List.mem_cons.mp hF with rfl|hF
    · simp only [List.flatMap_cons,List.length_append]
      omega
    · have H:=ih hF
      simp only [List.flatMap_cons,List.length_append]
      omega

omit [Nonempty S] [Nonempty ι] in
theorem NativeResourceMonomial.pairMomentBudget_of_canonical_bounds {i star : ℕ}
    {T : ClockTree S as} (P : NativeResourceMonomial i star T)
    (degree : ℕ) (hdegree : P.factors.length≤degree)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hm : ∀m∈P.tags,∀l : ℕ,0 < l → l≤degree →
      (pairClock (S:=S) as (m.cut i star)).disorderExpect w φ v q
        (fun σ=>|R (pairSpin as (m.cut i star) σ).1 (pairSpin as (m.cut i star) σ).2-C (m.cut i star)|^(2*l)) x₀≤
        (A*m.savedScale x W ε)^(2*l)) :
    P.PairMomentBudget w φ v q R C x₀ A x W ε := by
  intro e
  have hlen : 0 < P.factors.length := by have H:=e.isLt;omega
  exact hm (P.factors.get e).1 (List.mem_map.mpr ⟨P.factors.get e,List.get_mem _ e,rfl⟩)
    P.factors.length hlen hdegree

omit [Nonempty S] [Nonempty ι] in
theorem NativeResourceTerm.pairMomentBudget_of_canonical_bounds {i star : ℕ}
    {T : ClockTree S as} (P : NativeResourceTerm i star T)
    (degree : ℕ) (hdegree : P.resources.length≤degree)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hm : ∀m∈P.resources,∀l : ℕ,0 < l → l≤degree →
      (pairClock (S:=S) as (m.cut i star)).disorderExpect w φ v q
        (fun σ=>|R (pairSpin as (m.cut i star) σ).1 (pairSpin as (m.cut i star) σ).2-C (m.cut i star)|^(2*l)) x₀≤
        (A*m.savedScale x W ε)^(2*l)) :
    P.PairMomentBudget w φ v q R C x₀ A x W ε := by
  constructor
  · refine P.live.pairMomentBudget_of_canonical_bounds degree ?_ w φ v q R C x₀ A x W ε ?_
    · have H : P.live.tags.length≤P.resources.length := by
        simp only [NativeResourceTerm.resources,List.length_append]
        omega
      simpa only [NativeResourceMonomial.tags,List.length_map] using H.trans hdegree
    · intro m hmTag l hl hlD
      exact hm m (List.mem_append_right _ hmTag) l hl hlD
  · intro F hF
    refine F.monomial.pairMomentBudget_of_canonical_bounds degree ?_ w φ v q R C x₀ A x W ε ?_
    · have H:=native_frozen_tags_length_le P.frozen F hF
      have H' : (P.frozen.flatMap (fun G=>G.monomial.tags)).length≤P.resources.length := by
        simp only [NativeResourceTerm.resources,List.length_append]
        omega
      simpa only [NativeResourceMonomial.tags,List.length_map] using (H.trans H').trans hdegree
    · intro m hmTag l hl hlD
      exact hm m (List.mem_append_left _ (List.mem_flatMap.mpr ⟨F,hF,hmTag⟩)) l hl hlD

omit [Nonempty S] [Nonempty ι] in
theorem NativeActualResourceGenerated.pairMomentBudget_of_initial_star_bounds
    {i star U k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U [.initial] k T P)
    (degree : ℕ) (hd : 1+k≤degree)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hInitial : ∀l : ℕ,0 < l → l≤degree →
      (pairClock (S:=S) as i).disorderExpect w φ v q
        (fun σ=>|R (pairSpin as i σ).1 (pairSpin as i σ).2-C i|^(2*l)) x₀≤(A*x)^(2*l))
    (hStar : ∀l : ℕ,0 < l → l≤degree →
      (pairClock (S:=S) as star).disorderExpect w φ v q
        (fun σ=>|R (pairSpin as star σ).1 (pairSpin as star σ).2-C star|^(2*l)) x₀≤(A*(ε*W))^(2*l)) :
    P.PairMomentBudget w φ v q R C x₀ A x W ε := by
  refine P.pairMomentBudget_of_canonical_bounds degree ?_ w φ v q R C x₀ A x W ε ?_
  · rw [hP.total_factor_depth]
    simpa only [List.length_singleton] using hd
  · intro m hm l hl hlD
    rw [hP.resource_word] at hm
    rcases List.mem_append.mp hm with hm|hm
    · obtain rfl:=List.mem_singleton.mp hm
      exact hInitial l hl hlD
    · obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hm
      exact hStar l hl hlD

end OAI.SKFluctuations.Hierarchy.ClockTree
