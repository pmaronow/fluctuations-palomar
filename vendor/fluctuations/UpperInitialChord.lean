module

public import ActualWallDerivative
public import SKFluctuationsOAI.Probability.SKFluctuations.OrderedSKCumulativeChord

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem wall_massStepSum_add (as : List PositiveMass) (a : ℝ) (C D : ℕ → ℝ) :
    massStepSum as a (fun j => C j+D j) = massStepSum as a C+massStepSum as a D := by
  induction as generalizing a C D with
  | nil => simp only [massStepSum]; ring
  | cons b as ih => simp only [massStepSum, ih]; ring

theorem chord_penalty_eq_penalty_add_loss {e δ r : ℝ} (hres : δ < e) :
    (e*r)^2/(e-δ) = e*r^2+δ*e/(e-δ)*r^2 := by
  field_simp [(sub_pos.mpr hres).ne']
  ring

theorem finite_pressure_upper_chord
    (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ a ∈ as, a.val ≤ 1)
    (b₀ b₁ e r : ℕ → ℝ)
    (hres : ∀ j, b₀ j-b₁ j < e j)
    (hbchild : Monotone (fun j => b₀ j-e j))
    (hhchild : Monotone (fun j => e j*r j))
    (hbtarget : Monotone b₁)
    (hbc0 : 0 ≤ b₀ 0-e 0) (hhc0 : 0 ≤ e 0*r 0)
    (hb10 : 0 ≤ b₁ 0) (x : OrderedFeatureIndex n → ℝ) :
    orderedSKPressure n as b₁ (fun _ => 0) x ≤
      finiteCompensatedPressure n as b₀ (fun _ => 0) e r x +
        (1/4 : ℝ)*massStepSum as 0
          (fun j => (b₀ j-b₁ j)*e j/(e j-(b₀ j-b₁ j))*(r j)^2) := by
  have hc := orderedSK_cumulative_chord n hn as ho hu
    (fun j => b₀ j-e j) (fun j => e j*r j) b₁ (fun _ => 0)
    hbchild hhchild hbtarget (fun _ _ _ => le_rfl) hbc0 hhc0 hb10 (by norm_num)
    (fun j _ => by linarith [hres j])
    (fun j _ hz => by linarith [hres j]) x
  have halgebra (j : ℕ) :
      (e j*r j-0)^2/(b₁ j-(b₀ j-e j)) =
      e j*(r j)^2+(b₀ j-b₁ j)*e j/(e j-(b₀ j-b₁ j))*(r j)^2 := by
    rw [sub_zero, show b₁ j-(b₀ j-e j)=e j-(b₀ j-b₁ j) by ring]
    exact chord_penalty_eq_penalty_add_loss (hres j)
  simp_rw [halgebra] at hc
  rw [wall_massStepSum_add] at hc
  unfold finiteCompensatedPressure
  simp only [zero_add]
  linarith

theorem initial_chord_loss_le {ε e r R : ℝ}
    (hε : 0 ≤ ε) (he : 0 < e) (hres : 2*ε ≤ e) (hr : r^2 ≤ R^2) :
    ε*e/(e-ε)*r^2 ≤ 2*ε*R^2 := by
  have hp : 0 < e-ε := by linarith
  have hratio : ε*e/(e-ε) ≤ 2*ε := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hnonneg : 0 ≤ ε*e/(e-ε) := by positivity
  exact (mul_le_mul_of_nonneg_left hr hnonneg).trans
    (mul_le_mul_of_nonneg_right hratio (sq_nonneg R))

theorem below_wall_partitionSum_tendsto {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun k => massStepSum (uniformMasses k) 0
      (fun j => if partitionPoint 0 (uniformMasses k) j < s then (1 : ℝ) else 0))
      atTop (𝓝 s) := by
  have hmono : MonotoneOn (fun u : ℝ => if u < s then (-1 : ℝ) else 0) (Icc 0 1) := by
    intro u hu v hv huv
    by_cases hus : u < s
    · by_cases hvs : v < s <;> simp [hus, hvs]
    · have hvs : ¬v < s := by linarith
      simp [hus, hvs]
  have hlim := (partitionSum_tendsto hmono).neg
  have hfun (k : ℕ) : -(massStepSum (uniformMasses k) 0
      (fun j => if partitionPoint 0 (uniformMasses k) j < s then (-1 : ℝ) else 0)) =
      massStepSum (uniformMasses k) 0
        (fun j => if partitionPoint 0 (uniformMasses k) j < s then (1 : ℝ) else 0) := by
    have heq : (fun j => if partitionPoint 0 (uniformMasses k) j < s then (-1 : ℝ) else 0) =
        fun j => (-1 : ℝ)*(if partitionPoint 0 (uniformMasses k) j < s then (1 : ℝ) else 0) := by
      funext j
      split_ifs <;> norm_num
    rw [heq, massStepSum_const_mul]
    ring
  have hi : -(∫ u in (0 : ℝ)..1, if u < s then (-1 : ℝ) else 0) = s := by
    rw [integral_below_wall hs hs1 intervalIntegrable_const]
    simp
  simpa only [hfun, hi] using hlim

theorem path_pressure_initial_chord_bound
    (n : ℕ) (hn : 0 < n) {T ε s R error : ℝ} (_hT : 0 < T)
    (hε : 0 ≤ ε) (hεT : ε ≤ T) (hs : 0 < s) (hs1 : s ≤ 1)
    (e r : ℝ → ℝ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 < e u)
    (hbc : MonotoneOn (fun u => T-e u) (Icc (0 : ℝ) 1))
    (hhc : MonotoneOn (fun u => e u*r u) (Icc (0 : ℝ) 1))
    (hbc0 : 0 ≤ T-e 0) (hhc0 : 0 ≤ e 0*r 0)
    (hp : MonotoneOn (fun u => e u*(r u)^2) (Icc (0 : ℝ) 1))
    (hres : ∀ u ∈ Icc (0 : ℝ) 1, u < s → 2*ε ≤ e u)
    (hr : ∀ u ∈ Icc (0 : ℝ) 1, u < s → (r u)^2 ≤ R^2)
    (x : OrderedFeatureIndex n → ℝ)
    (hcomp : pathCompensatedPressure n (fun _ => T) (fun _ => 0) e r x ≤
      realOrderedSKPathPressure n (fun _ => T) (fun _ => 0) x+error) :
    realOrderedSKPathPressure n (fun u => if u < s then T-ε else T) (fun _ => 0) x-
      realOrderedSKPathPressure n (fun _ => T) (fun _ => 0) x ≤ ε*R^2*s/2+error := by
  let b₁ : ℝ → ℝ := fun u => if u < s then T-ε else T
  have hb1 : MonotoneOn b₁ (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    by_cases hus : u < s
    · by_cases hvs : v < s
      · simp [b₁, hus, hvs]
      · simp [b₁, hus, hvs]; linarith
    · have hvs : ¬v < s := by linarith
      simp [b₁, hus, hvs]
  have hb10 : 0 ≤ b₁ 0 := by simp [b₁, hs, hεT]
  have hfinite (k : ℕ) :
      orderedSKPressure n (uniformMasses k)
        (fun j => b₁ (partitionPoint 0 (uniformMasses k) j)) (fun _ => 0) x ≤
      finiteCompensatedPressure n (uniformMasses k) (fun _ => T) (fun _ => 0)
        (fun j => e (partitionPoint 0 (uniformMasses k) j))
        (fun j => r (partitionPoint 0 (uniformMasses k) j)) x +
      ε*R^2/2*massStepSum (uniformMasses k) 0
        (fun j => if partitionPoint 0 (uniformMasses k) j < s then (1 : ℝ) else 0) := by
    let u := fun j => partitionPoint 0 (uniformMasses k) j
    have hu (j : ℕ) : u j ∈ Icc (0 : ℝ) 1 := partitionPoint_mem _ (uniformMasses_ordered k) j
    have hres' (j : ℕ) : T-b₁ (u j) < e (u j) := by
      by_cases hus : u j < s
      · simp only [b₁, ite_eq_left hus]
        have hh := hres _ (hu j) hus
        have hhpos := he _ (hu j)
        linarith
      · simp only [b₁, ite_eq_right hus, sub_self]
        exact he _ (hu j)
    have hc := finite_pressure_upper_chord n hn (uniformMasses k)
      (uniformMasses_ordered k).pairwise (uniformMasses_ordered k).members_le_one
      (fun _ => T) (fun j => b₁ (u j)) (fun j => e (u j)) (fun j => r (u j)) hres'
      (comp_partitionPoint_monotone hbc _ (uniformMasses_ordered k))
      (comp_partitionPoint_monotone hhc _ (uniformMasses_ordered k))
      (comp_partitionPoint_monotone hb1 _ (uniformMasses_ordered k))
      (by simpa [u, partitionPoint] using hbc0) (by simpa [u, partitionPoint] using hhc0)
      (by simpa [u, partitionPoint] using hb10) x
    have hcost := massStepSum_mono (uniformMasses k) (uniformMasses_ordered k) (fun j _ => by
      show (T-b₁ (u j))*e (u j)/(e (u j)-(T-b₁ (u j)))*(r (u j))^2 ≤
        (2*ε*R^2)*(if u j < s then (1 : ℝ) else 0)
      by_cases hus : u j < s
      · simp only [b₁, ite_eq_left hus, sub_sub_cancel, mul_one]
        exact initial_chord_loss_le hε (he _ (hu j)) (hres _ (hu j) hus) (hr _ (hu j) hus)
      · simp [b₁, hus])
    rw [massStepSum_const_mul] at hcost
    have hcost' := mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 1/4)
    dsimp only [u] at hc hcost'
    calc
      _ ≤ _ := hc
      _ ≤ _ := by linarith
  have ht := orderedSKPressure_samples_tendsto n hn b₁ (fun _ => 0) hb1
    (fun _ _ _ _ _ => le_rfl) hb10 (by norm_num) x
  have hc := finiteCompensatedPressure_tendsto_path n hn (fun _ => T) (fun _ => 0)
    e r hbc (by simpa only [zero_add] using hhc) hbc0
    (by simpa only [zero_add] using hhc0) hp x
  have hb := (below_wall_partitionSum_tendsto hs hs1).const_mul (ε*R^2/2)
  have hh := le_of_tendsto_of_tendsto ht (hc.add hb) (Filter.Eventually.of_forall hfinite)
  dsimp only [b₁] at hh
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
