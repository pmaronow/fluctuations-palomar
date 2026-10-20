module

public import CavityActualFrozenInsertion
public import CavityFiniteProfilePermutation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem cutLSlope_one_coordinate_abs_le (n U N : ℕ) (b h K : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ j, j ≤ N → |b j| ≤ B ∧ |h j| ≤ B ∧ |K j| ≤ B)
    (j : ℕ) (hj : j ≤ N) (i : FullCoordinate n) :
    |cutLSlope n U 1 b h K j i| ≤ B := by
  have H := hc j hj
  rcases i with (i|i)|(i|i) <;>
    simp only [cutLSlope,fullVariance] <;> split_ifs <;>
      simp only [Pi.zero_apply,Sum.elim_inl,Sum.elim_inr,sub_self,zero_mul,one_mul,abs_zero]
  all_goals first | exact hB | exact H.1 | exact H.2.1

 theorem cutTSlope_zero_coordinate_abs_le (n U N : ℕ) (b h K : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ j, j ≤ N → |b j| ≤ B ∧ |h j| ≤ B ∧ |K j| ≤ B)
    (j : ℕ) (hj : j ≤ N) (i : FullCoordinate n) :
    |cutTSlope n U 0 b h K j i| ≤ B := by
  have H := hc j hj
  rcases i with (i|i)|(i|i) <;>
    simp only [cutTSlope,rowInterpolationSlope,relocatedClock,Sum.elim_inl,Sum.elim_inr]
  all_goals try split_ifs
  all_goals try simp only [zero_mul,neg_zero,abs_zero,abs_neg]
  all_goals first | exact hB | exact H.1 | exact H.2.1 | exact H.2.2

 theorem cutFrozenLowHighJet_oneError_moment_budget (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r k : ℕ} (hT : T.leaves ≤ r) (hk : 0 < k)
    {C rho B : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho) (hB : 0 ≤ B)
    (hP : ∀ σ, |P σ| ≤ C)
    (hc : ∀ j, j ≤ as.length → |b j| ≤ B ∧ |h j| ≤ B ∧ |K j| ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ j, j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => |ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*k)) x ≤ rho^(2*k)) :
    |cutFrozenLowHighJet n q U b h K T P x k 1 t| ≤
      ClockTree.pairForkVariation r*ClockTree.absJetVariation (r+2) k*C*rho^k*
        (T.forkCost D + (∫ u, ClockTree.edgeDensity 0 as D u)) := by
  rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho P x hq0 hq hb hh hK hbm hhm hKm k 1 ht]
  have hF : ∀ σ i, (fullFeature n σ (Pi.single i 1))^2=(fullAmplitude n i)^2 := by
    intro σ i
    rw [fullFeature_single_any_decidable]
    simpa only [fullFeature_single] using fullFeature_square n σ i
  have hDirs : ∀ L ∈ List.replicate k (cutLSlope n U 1 b h K)++cutTSlope n U 0 b h K::[],
      ∀ j, j ≤ as.length → ∀ i, |L j i| ≤ B := by
    intro L hL j hj i
    rcases List.mem_append.mp hL with hL|hL
    · have he := List.mem_replicate.mp hL
      rw [he.2]
      exact cutLSlope_one_coordinate_abs_le n U as.length b h K hB hc j hj i
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hL
      rw [hL]
      exact cutTSlope_zero_coordinate_abs_le n U as.length b h K hB hc j hj i
  have H := T.disorderProfileJets_oneError_finite_moment_L2 (fullWeight_pos n) (fullFeature n)
    (fun i => (fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i)
    ho 0 (cutFullVariance n q U 0 t b h K)
    (fun i => cutFullVariance_monotone n q U (by norm_num) ht hq hb hh hK hbm hhm hKm i)
    (fun i => cutFullVariance_nonneg n q U (by norm_num) ht hq0 hb hh hK 0 i)
    (cutTSlope n U 0 b h K) (List.replicate k (cutLSlope n U 1 b h K)) []
    (by simpa only [List.append_nil,List.length_replicate] using hk) hB hDirs hC hrho hT P hP x hD
    hsecond (by
      intro L hL j hj
      simp only [List.append_nil] at hL
      have he := List.mem_replicate.mp hL
      rw [he.2]
      simpa only [List.append_nil,List.length_replicate] using hmoment j hj)
  simpa only [List.map_append,List.map_replicate,List.append_nil,List.map_cons,List.map_nil,
    List.replicate_one,List.length_replicate] using H

end OAI.SKFluctuations.Cavity
