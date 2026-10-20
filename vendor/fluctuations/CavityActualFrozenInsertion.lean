module

public import CavityFrozenProfileJets

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy GaussianCalculus

 theorem cutLowDirection_at_one (n U : ℕ) (b h K : ℕ → ℝ) :
    (fun j i => cutLSlope n U 0 b h K j i+1*cutLowError n U b h K j i) =
      cutLSlope n U 1 b h K := by
  funext j i
  rcases i with (i|i)|(i|i) <;>
    simp only [cutLSlope,cutLowError] <;> split_ifs <;>
      simp [fullVariance,rowInterpolationSlope]

 theorem cutLowDirection_at_one_apply (n U : ℕ) (b h K : ℕ → ℝ)
    (j : ℕ) (i : FullCoordinate n) :
    cutLSlope n U 0 b h K j i+1*cutLowError n U b h K j i =
      cutLSlope n U 1 b h K j i :=
  congrFun (congrFun (cutLowDirection_at_one n U b h K) j) i

private theorem two_scale_monotone (U : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {f : ℕ → ℝ} (hf : Monotone f) (hf0 : ∀ j, 0 ≤ f j) :
    Monotone (fun j => if j < U then s*f j else t*f j) := by
  intro j k hjk
  by_cases hj : j<U <;> by_cases hk : k<U
  · simpa only [hj,hk,ite_true] using mul_le_mul_of_nonneg_left (hf hjk) hs
  · simp only [hj,hk,ite_true,ite_false]
    exact (mul_le_mul_of_nonneg_right hst (hf0 j)).trans
      (mul_le_mul_of_nonneg_left (hf hjk) (hs.trans hst))
  · exact False.elim (hj (lt_of_le_of_lt hjk hk))
  · simpa only [hj,hk,ite_false] using
      mul_le_mul_of_nonneg_left (hf hjk) (hs.trans hst)

 theorem cutFrozenAffine_monotone (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (i : FullCoordinate n) :
    Monotone (fun j => cutFullVariance n q U 0 t b h K j i+s*cutLSlope n U 1 b h K j i) := by
  rcases i with (i|i)|(i|i)
  · convert hq i using 1
    funext j
    simp only [cutFullVariance,fullVariance,cutLSlope]
    split_ifs <;> simp
  · have H := (relocatedClock_monotone U (show (0:ℝ) ∈ Icc 0 1 by norm_num) hKm hK)
    intro j k hjk
    have h := mul_le_mul_of_nonneg_left (H hjk) (sub_nonneg.mpr ht)
    convert h using 1 <;> simp only [cutFullVariance,fullVariance,cutLSlope] <;>
      split_ifs <;> simp
  · have H := two_scale_monotone U hs hst hbm hb
    convert H using 1
    funext j
    by_cases hj : j<U <;> simp [cutFullVariance,fullVariance,cutLSlope,relocatedClock,hj]
  · have H := two_scale_monotone U hs hst hhm hh
    convert H using 1
    funext j
    by_cases hj : j<U <;> simp [cutFullVariance,fullVariance,cutLSlope,relocatedClock,hj]

 theorem cutFrozenAffine_nonneg (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ)
    (b h K : ℕ → ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : t ∈ Icc (0:ℝ) 1)
    (hq0 : ∀ j i, 0 ≤ q j i) (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j)
    (hK : ∀ j, 0 ≤ K j) (j : ℕ) (i : FullCoordinate n) :
    0 ≤ cutFullVariance n q U 0 t b h K j i+s*cutLSlope n U 1 b h K j i := by
  apply add_nonneg (cutFullVariance_nonneg n q U (by norm_num) ht hq0 hb hh hK j i)
  apply mul_nonneg hs
  unfold cutLSlope
  split_ifs
  · exact fullVariance_nonneg n 0 (by intro i; simp) (by norm_num) (hb j) (hh j) (hK j) i
  · simp

 theorem cutFrozenLowHighJet_zero_eq_profileJets (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    cutFrozenLowHighJet n q U b h K T P x k 0 t =
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 t b h K) x
        (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K))) T P := by
  have hp : ∀ s ∈ Ioo (0:ℝ) t, ∀ i, Monotone (fun j =>
      cutFullVariance n q U 0 t b h K j i+s*(cutLSlope n U 0 b h K j i+1*cutLowError n U b h K j i)) := by
    simp only [cutLowDirection_at_one_apply]
    intro s hs i
    exact cutFrozenAffine_monotone n q U b h K hs.1.le hs.2.le ht.2.le hq hb hh hK hbm hhm hKm i
  have hr : ∀ s ∈ Ioo (0:ℝ) t, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutFullVariance n q U 0 t b h K 0 i+s*(cutLSlope n U 0 b h K 0 i+1*cutLowError n U b h K 0 i) := by
    simp only [cutLowDirection_at_one_apply]
    intro s hs i
    exact cutFrozenAffine_nonneg n q U b h K hs.1.le ⟨ht.1.le,ht.2.le⟩ hq0 hb hh hK 0 i
  have H := ClockPolynomial.finiteLowJet_eq_profileJets_zero (fullWeight_pos n) (fullFeature n)
    T ho P (cutLSlope n U 0 b h K) (cutLowError n U b h K) 1 0
    (cutFullVariance n q U 0 t b h K) x ht.1 hp hr k
  simpa only [cutFrozenLowHighJet,ClockPolynomial.finiteIterInsert,cutLowDirection_at_one] using H

 theorem cutFrozenLowHighJet_eq_profileJets_interior (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (k r : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    cutFrozenLowHighJet n q U b h K T P x k r t =
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 t b h K) x
        ((List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)))++
         List.replicate r (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K))) T P := by
  induction r generalizing t with
  | zero =>
    simpa only [List.replicate_zero,List.append_nil] using
      cutFrozenLowHighJet_zero_eq_profileJets n q U b h K T ho P x hq0 hq hb hh hK hbm hhm hKm k ht
  | succ r ih =>
    let Ks := (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)))++
      List.replicate r (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K))
    have he : (cutFrozenLowHighJet n q U b h K T P x k r) =ᶠ[𝓝 t]
        (fun s => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U 0 s b h K) x Ks T P) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact ih hs
    have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
        cutTBase n q U 0 b h K 0 i+s*cutTSlope n U 0 b h K 0 i := by
      intro s hs i
      have hn := cutFullVariance_nonneg n q U (l := 0) (t := s)
        (by norm_num) ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
      simpa only [cutFullVariance_t_affine,Pi.zero_apply] using hn
    have hj := ClockTree.hasDerivAt_finiteProfileJets (fullWeight_pos n) (fullFeature n) ho 0
      (cutTBase n q U 0 b h K) (cutTSlope n U 0 b h K)
      (cutT_affine_monotone n q U (by norm_num) hq hb hh hK hbm hhm hKm) hr Ks T P x ht
    have hd := cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK hbm hhm hKm ho P x k r ht
    calc
      _ = deriv (cutFrozenLowHighJet n q U b h K T P x k r) t := hd.deriv.symm
      _ = deriv (fun s => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U 0 s b h K) x Ks T P) t := he.deriv_eq
      _ = _ := by
        simpa only [cutFullVariance_t_affine,Ks,List.replicate_succ',List.append_assoc] using hj.deriv

 theorem cutFrozenLowHighJet_eq_profileJets (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
    (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (k r : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    cutFrozenLowHighJet n q U b h K T P x k r t =
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 t b h K) x
        ((List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)))++
         List.replicate r (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K))) T P := by
  have he : Set.EqOn (cutFrozenLowHighJet n q U b h K T P x k r)
      (fun s => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U 0 s b h K) x
        ((List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 1 b h K)))++
         List.replicate r (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K))) T P)
      (Ioo (0:ℝ) 1) := by
    intro s hs
    exact cutFrozenLowHighJet_eq_profileJets_interior n q U b h K T ho P x hq0 hq hb hh hK hbm hhm hKm k r hs
  have H := he.closure (cutFrozenLowHighJet_continuous n q U b h K T P x k r)
    (ClockTree.disorderProfileJets_continuous (fullWeight_pos n) (fullFeature n) ho 0
      (fun s => cutFullVariance n q U 0 s b h K) (cutFullVariance_continuous_t n q U b h K 0)
      (fun _ => x) continuous_const _ T P)
  apply H
  simpa only [closure_Ioo (show (0:ℝ)≠1 by norm_num)] using ht

end OAI.SKFluctuations.Cavity
