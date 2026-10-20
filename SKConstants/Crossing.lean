module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Measure.Real

public section

namespace SKConstants

variable {V : Type*}

@[expose] def graphCutBoundary (G : SimpleGraph V) (A : Set V) : Set V :=
  {u | u ∈ A ∧ ∃ v, v ∉ A ∧ G.Adj u v}

@[expose] def graphBoundaryNeighborhood (G : SimpleGraph V) (A : Set V) (R : ℕ) : Set V :=
  {u | ∃ v ∈ graphCutBoundary G A, G.edist u v ≤ (R : ℕ∞)}

@[expose] def graphTwoSidedBoundary (G : SimpleGraph V) (A : Set V) : Set V :=
  graphCutBoundary G A ∪ graphCutBoundary G Aᶜ

@[expose] def graphTwoSidedBoundaryNeighborhood (G : SimpleGraph V) (A : Set V) (R : ℕ) : Set V :=
  graphBoundaryNeighborhood G A R ∪ graphBoundaryNeighborhood G Aᶜ R

theorem mem_graphTwoSidedBoundaryNeighborhood_iff (G : SimpleGraph V) (A : Set V)
    (R : ℕ) (u : V) :
    u ∈ graphTwoSidedBoundaryNeighborhood G A R ↔
      ∃ b ∈ graphTwoSidedBoundary G A, G.edist u b ≤ (R : ℕ∞) := by
  simp only [graphTwoSidedBoundaryNeighborhood, graphBoundaryNeighborhood,
    graphTwoSidedBoundary, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨b, hb, hdist⟩ | ⟨b, hb, hdist⟩)
    · exact ⟨b, Or.inl hb, hdist⟩
    · exact ⟨b, Or.inr hb, hdist⟩
  · rintro ⟨b, hb | hb, hdist⟩
    · exact Or.inl ⟨b, hb, hdist⟩
    · exact Or.inr ⟨b, hb, hdist⟩

theorem sampled_cut_crossing (A : Set V) (f : ℕ → V) (n : ℕ)
    (hstart : f 0 ∈ A) (hend : f n ∉ A) :
    ∃ i < n, f i ∈ A ∧ f (i + 1) ∉ A := by
  induction n with
  | zero => exact False.elim (hend hstart)
  | succ n ih =>
      by_cases hn : f n ∈ A
      · exact ⟨n, Nat.lt_succ_self n, hn, hend⟩
      · obtain ⟨i, hi, hcut⟩ := ih hn
        exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n), hcut⟩

theorem walk_boundary_prefix (G : SimpleGraph V) (A : Set V)
    {u v : V} (w : G.Walk u v) (hu : u ∈ A) (hv : v ∉ A) :
    ∃ b ∈ graphCutBoundary G A, b ∈ w.support ∧
      ∃ preWalk : G.Walk u b, preWalk.length ≤ w.length := by
  induction w with
  | nil => exact False.elim (hv hu)
  | @cons u v z huv w ih =>
      by_cases hvmem : v ∈ A
      · obtain ⟨b, hb, hsupport, preWalk, hlength⟩ := ih hvmem hv
        refine ⟨b, hb, ?_, SimpleGraph.Walk.cons huv preWalk, ?_⟩
        · exact List.mem_cons_of_mem u hsupport
        · simpa only [SimpleGraph.Walk.length_cons] using Nat.add_le_add_right hlength 1
      · refine ⟨u, ⟨hu, v, hvmem, huv⟩, ?_, SimpleGraph.Walk.nil, ?_⟩
        · simp
        · simp

theorem close_opposite_endpoints_near_boundary (G : SimpleGraph V) (A : Set V)
    {u v : V} {R : ℕ} (hu : u ∈ A) (hv : v ∉ A)
    (hclose : G.edist u v ≤ (R : ℕ∞)) :
    u ∈ graphBoundaryNeighborhood G A R := by
  have hfinite : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (by simp) hclose
  obtain ⟨w, hw⟩ := G.exists_walk_of_edist_ne_top hfinite
  obtain ⟨b, hb, _, preWalk, hlength⟩ := walk_boundary_prefix G A w hu hv
  refine ⟨b, hb, (G.edist_le preWalk).trans ?_⟩
  exact (ENat.natCast_le_natCast.mpr hlength).trans
    (hw.trans_le hclose)

theorem close_opposite_endpoints_near_twoSidedBoundary (G : SimpleGraph V)
    (A : Set V) {u v : V} {R : ℕ} (hu : u ∈ A) (hv : v ∉ A)
    (hclose : G.edist u v ≤ (R : ℕ∞)) :
    u ∈ graphTwoSidedBoundaryNeighborhood G A R ∧
      v ∈ graphTwoSidedBoundaryNeighborhood G A R := by
  constructor
  · exact Or.inl (close_opposite_endpoints_near_boundary G A hu hv hclose)
  · apply Or.inr
    apply close_opposite_endpoints_near_boundary G Aᶜ hv
    · exact fun h => h hu
    · rw [G.edist_comm]
      exact hclose

theorem coarse_sampled_path_hits_twoSidedBoundary (G : SimpleGraph V) (A : Set V)
    (f : ℕ → V) (coarse : ℕ → Prop) (n R : ℕ)
    (hstart : f 0 ∈ A) (hend : f n ∉ A)
    (hsteps : ∀ i < n, G.edist (f i) (f (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ i < n, coarse i ∨ coarse (i + 1)) :
    ∃ i ≤ n, coarse i ∧ f i ∈ graphTwoSidedBoundaryNeighborhood G A R := by
  obtain ⟨i, hi, hin, hout⟩ := sampled_cut_crossing A f n hstart hend
  obtain ⟨hleft, hright⟩ := close_opposite_endpoints_near_twoSidedBoundary G A
    hin hout (hsteps i hi)
  rcases hcoarse i hi with hflag | hflag
  · exact ⟨i, Nat.le_of_lt hi, hflag, hleft⟩
  · exact ⟨i + 1, Nat.succ_le_of_lt hi, hflag, hright⟩

theorem sampled_path_hits_boundary_neighborhood (G : SimpleGraph V) (A : Set V)
    (f : ℕ → V) (n R : ℕ) (hstart : f 0 ∈ A) (hend : f n ∉ A)
    (hsteps : ∀ i < n, G.edist (f i) (f (i + 1)) ≤ (R : ℕ∞)) :
    ∃ i < n, f i ∈ graphBoundaryNeighborhood G A R := by
  obtain ⟨i, hi, hin, hout⟩ := sampled_cut_crossing A f n hstart hend
  exact ⟨i, hi, close_opposite_endpoints_near_boundary G A hin hout (hsteps i hi)⟩

theorem sampled_path_hits_boundary_of_dist (G : SimpleGraph V) (A : Set V)
    (f : ℕ → V) (n R : ℕ) (hstart : f 0 ∈ A) (hend : f n ∉ A)
    (hreachable : ∀ i < n, G.Reachable (f i) (f (i + 1)))
    (hsteps : ∀ i < n, G.dist (f i) (f (i + 1)) ≤ R) :
    ∃ i < n, f i ∈ graphBoundaryNeighborhood G A R := by
  apply sampled_path_hits_boundary_neighborhood G A f n R hstart hend
  intro i hi
  rw [← (hreachable i hi).coe_dist_eq_edist]
  exact ENat.natCast_le_natCast.mpr (hsteps i hi)

open MeasureTheory

theorem measure_toReal_le_div_of_inter_subset
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {W C H : Set Ω} {p : ℝ}
    (hp : 0 < p) (hH : μ H ≠ ⊤) (hsubset : W ∩ C ⊆ H)
    (hlower : p * (μ W).toReal ≤ (μ (W ∩ C)).toReal) :
    (μ W).toReal ≤ (μ H).toReal / p := by
  apply (le_div_iff₀ hp).2
  rw [mul_comm]
  exact hlower.trans (ENNReal.toReal_mono hH (measure_mono hsubset))

theorem measure_toReal_le_div_of_inter_subset_of_finite
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {W C H : Set Ω} {p : ℝ} (hp : 0 < p) (hsubset : W ∩ C ⊆ H)
    (hlower : p * (μ W).toReal ≤ (μ (W ∩ C)).toReal) :
    (μ W).toReal ≤ (μ H).toReal / p :=
  measure_toReal_le_div_of_inter_subset μ hp (measure_ne_top μ H) hsubset hlower

theorem probability_le_div_of_inter_subset
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {W C H : Set Ω} {p : ℝ} (hp : 0 < p) (hsubset : W ∩ C ⊆ H)
    (hlower : p * μ.real W ≤ μ.real (W ∩ C)) :
    μ.real W ≤ μ.real H / p :=
  measure_toReal_le_div_of_inter_subset_of_finite μ hp hsubset hlower

theorem probability_sampled_path_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : SimpleGraph V) (A : Set V) (f : Ω → ℕ → V) (n R : ℕ)
    {W C : Set Ω} {p : ℝ} (hp : 0 < p)
    (hstart : ∀ ω ∈ W ∩ C, f ω 0 ∈ A)
    (hend : ∀ ω ∈ W ∩ C, f ω n ∉ A)
    (hsteps : ∀ ω ∈ W ∩ C, ∀ i < n,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hlower : p * μ.real W ≤ μ.real (W ∩ C)) :
    μ.real W ≤ μ.real {ω | ∃ i < n,
      f ω i ∈ graphBoundaryNeighborhood G A R} / p := by
  apply probability_le_div_of_inter_subset μ hp _ hlower
  intro ω hω
  exact sampled_path_hits_boundary_neighborhood G A (f ω) n R
    (hstart ω hω) (hend ω hω) (hsteps ω hω)

theorem probability_coarse_sampled_path_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : SimpleGraph V) (A : Set V) (f : Ω → ℕ → V)
    (coarse : Ω → ℕ → Prop) (n R : ℕ)
    {W C : Set Ω} {p : ℝ} (hp : 0 < p)
    (hstart : ∀ ω ∈ W ∩ C, f ω 0 ∈ A)
    (hend : ∀ ω ∈ W ∩ C, f ω n ∉ A)
    (hsteps : ∀ ω ∈ W ∩ C, ∀ i < n,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω ∈ W ∩ C, ∀ i < n,
      coarse ω i ∨ coarse ω (i + 1))
    (hlower : p * μ.real W ≤ μ.real (W ∩ C)) :
    μ.real W ≤ μ.real {ω | ∃ i ≤ n, coarse ω i ∧
      f ω i ∈ graphTwoSidedBoundaryNeighborhood G A R} / p := by
  apply probability_le_div_of_inter_subset μ hp _ hlower
  intro ω hω
  exact coarse_sampled_path_hits_twoSidedBoundary G A (f ω) (coarse ω) n R
    (hstart ω hω) (hend ω hω) (hsteps ω hω) (hcoarse ω hω)

end SKConstants
