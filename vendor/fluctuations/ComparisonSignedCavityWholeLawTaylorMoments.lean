module

public import ComparisonSignedCavityWholeLawZeroLowError
public import ComparisonSignedCavityQuantitativeTaylorPhysical

@[expose] public section

noncomputable section
set_option maxHeartbeats 7500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy
 theorem cutFrozenLowHighJet_oneError_wholeLaw_moment_budget (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r k : ℕ} (hT : T.leaves ≤ r) (hk : 0 < k)
    {C rho B : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho) (hB : 0 ≤ B)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K) (fun σ=>|P σ|^4) x ≤ C^4)
    (hc : ∀ j, j ≤ as.length → |b j| ≤ B ∧ |h j| ≤ B ∧ |K j| ≤ B)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ j, j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => |ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) x ≤ rho^(4*k)) :
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
  have hperm : (List.replicate k (cutLSlope n U 1 b h K)++cutTSlope n U 0 b h K::[]).Perm
      (cutTSlope n U 0 b h K::List.replicate k (cutLSlope n U 1 b h K)):=by
    simpa only [List.append_nil] using
      (List.perm_middle (a:=cutTSlope n U 0 b h K)
        (l₁:=List.replicate k (cutLSlope n U 1 b h K)) (l₂:=[]))
  have HE:=T.actual_profileJets_perm_finite (fullWeight_pos n) (fullFeature n) ho 0
    (cutFullVariance n q U 0 t b h K)
    (fun i=>cutFullVariance_monotone n q U (by norm_num) ht hq hb hh hK hbm hhm hKm i)
    (fun i=>cutFullVariance_nonneg n q U (by norm_num) ht hq0 hb hh hK 0 i)
    hB hperm hDirs P x
  simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil,List.replicate_one] at HE ⊢
  rw [HE]
  have H:=T.disorderProfileJets_errorFirst_finite_wholeLaw_moment_L2 (fullWeight_pos n) (fullFeature n)
    (fun i=>(fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i) ho 0 (cutFullVariance n q U 0 t b h K) x
    (fun i=>cutFullVariance_monotone n q U (by norm_num) ht hq hb hh hK hbm hhm hKm i)
    (fun i=>cutFullVariance_nonneg n q U (by norm_num) ht hq0 hb hh hK 0 i)
    (cutTSlope n U 0 b h K) (List.replicate k (cutLSlope n U 1 b h K))
    (by simpa only [List.length_replicate] using hk) hB
    (fun L hL=>hDirs L (hperm.mem_iff.mpr hL)) hC hrho hT P hP hD hsecond
    (by
      intro L hL j hj
      have HE:=List.mem_replicate.mp hL
      rw [HE.2]
      simpa only [List.length_replicate] using hmoment j hj)
  simpa only [List.map_cons,List.map_replicate,List.length_replicate] using H

 theorem cutFrozenLowHighJet_twoError_wholeLaw_moment_budget (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r k : ℕ} (hT : T.leaves ≤ r)
    {C rho B M p : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho) (hB : 0 ≤ B) (hM : 0 ≤ M) (hp : 2 < p)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K) (fun σ=>|P σ|^(2*(p/(p-2)))) x ≤ C^(2*(p/(p-2))))
    (hc : ∀ j, j ≤ as.length → |b j| ≤ B ∧ |h j| ≤ B ∧ |K j| ≤ B)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hA : ∀ j, j ≤ as.length → ∀ σ τ, |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ| ≤ M)
    (hsecond : ∀ j, j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ j, j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 t b h K)
      (fun σ => |ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^((2*(p/(p-2)))*(k:ℝ))) x ≤ rho^((2*(p/(p-2)))*(k:ℝ))) :
    |cutFrozenLowHighJet n q U b h K T P x k 2 t| ≤
      ClockTree.pairForkVariation r*ClockTree.pairForkVariation (r+2)*ClockTree.absJetVariation (r+4) k*C*M^((p-2)/p)*M^((p-2)/p)*rho^k*
        (T.forkCost (fun j => D j^(4/p)) + (∫ u, ClockTree.edgeDensity 0 as (fun j => D j^(4/p)) u)) := by
  rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho P x hq0 hq hb hh hK hbm hhm hKm k 2 ht]
  have hF : ∀ σ i, (fullFeature n σ (Pi.single i 1))^2=(fullAmplitude n i)^2 := by
    intro σ i
    rw [fullFeature_single_any_decidable]
    simpa only [fullFeature_single] using fullFeature_square n σ i
  have hDirs : ∀ L ∈ List.replicate k (cutLSlope n U 1 b h K)++List.replicate 2 (cutTSlope n U 0 b h K),
      ∀ j, j ≤ as.length → ∀ i, |L j i| ≤ B := by
    intro L hL j hj i
    rcases List.mem_append.mp hL with hL|hL
    · have he := List.mem_replicate.mp hL
      rw [he.2]
      exact cutLSlope_one_coordinate_abs_le n U as.length b h K hB hc j hj i
    · have he := List.mem_replicate.mp hL
      rw [he.2]
      exact cutTSlope_zero_coordinate_abs_le n U as.length b h K hB hc j hj i
  have hperm : (List.replicate k (cutLSlope n U 1 b h K)++List.replicate 2 (cutTSlope n U 0 b h K)).Perm
      (List.replicate 2 (cutTSlope n U 0 b h K)++List.replicate k (cutLSlope n U 1 b h K)) := List.perm_append_comm
  have HE := T.actual_profileJets_perm_finite (fullWeight_pos n) (fullFeature n) ho
    0 (cutFullVariance n q U 0 t b h K)
    (fun i => cutFullVariance_monotone n q U (by norm_num) ht hq hb hh hK hbm hhm hKm i)
    (fun i => cutFullVariance_nonneg n q U (by norm_num) ht hq0 hb hh hK 0 i)
    hB hperm hDirs P x
  simp only [List.map_append,List.map_replicate] at HE
  rw [HE]
  have H := T.disorderProfileJets_twoErrorFirst_finite_wholeLaw_moment_L2 (fullWeight_pos n) (fullFeature n)
    (fun i => (fullAmplitude n i)^2) (by
      intro σ i
      rw [fullFeature_single_any_decidable]
      simpa only [fullFeature_single] using fullFeature_square n σ i)
    ho 0 (cutFullVariance n q U 0 t b h K) x
    (fun i => cutFullVariance_monotone n q U (by norm_num) ht hq hb hh hK hbm hhm hKm i)
    (fun i => cutFullVariance_nonneg n q U (by norm_num) ht hq0 hb hh hK 0 i)
    (cutTSlope n U 0 b h K) (List.replicate k (cutLSlope n U 1 b h K))
    hB (by
      intro L hL j hj i
      apply hDirs L _ j hj i
      exact hperm.mem_iff.mpr (by simpa [List.replicate_succ,List.replicate_zero] using hL))
    hC hM hrho hp hT P hP hA hD hsecond (by
      intro L hL j hj
      have he := List.mem_replicate.mp hL
      rw [he.2]
      simpa only [List.length_replicate] using hmoment j hj)
  simpa only [List.map_append,List.map_replicate,List.append_nil,List.map_cons,List.map_nil,
    List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.length_replicate] using H

end OAI.SKFluctuations.Cavity
