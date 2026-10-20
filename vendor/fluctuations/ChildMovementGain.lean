module

public import SKFluctuationsOAI.Probability.SKFluctuations.OrderedSKCumulativeChord
public import SKFluctuationsOAI.Probability.SKFluctuations.VarianceTestZeroRoot

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy

theorem movement_strength_positive {e D eh omega : ℝ}
    (he : 0   ≤   e) (hD : 0<D) (hw0 : 0   ≤   omega) (hw : omega<D/(e+D))
    (hh : eh   ≤   e/(1-omega)) :
    0<1-omega ∧ 0<e+D-eh := by
  have hA : 0<e+D := by linarith
  have hAD : D/(e+D)   ≤   1 := (div_le_one₀ hA).mpr (by linarith)
  have hw1 : 0<1-omega := by linarith
  have hh' := (le_div_iff₀ hw1).mp hh
  have hgap := (lt_div_iff₀ hA).mp hw
  have hprod : 0<(e+D-eh)*(1-omega) := by nlinarith
  exact ⟨hw1,(mul_pos_iff.mp hprod).resolve_right (by intro h; linarith [h.2]) |>.1⟩

theorem movement_pointwise_gain {e D eh omega r z : ℝ}
    (he : 0   ≤   e) (hD : 0<D) (hw0 : 0   ≤   omega) (hw : omega<D/(e+D))
    (hh : eh   ≤   e/(1-omega)) :
    e*omega*(z-r)^2   ≤   e*r^2+D*z^2-eh*(r+omega*(z-r))^2-
      (e*r+D*z-eh*(r+omega*(z-r)))^2/(e+D-eh) := by
  obtain ⟨hw1,ha⟩ := movement_strength_positive he hD hw0 hw hh
  have hA : 0<e+D := by linarith
  have hg : 0   ≤   D-(e+D)*omega := by linarith [(lt_div_iff₀ hA).mp hw]
  have hh' : 0   ≤   e-eh*(1-omega) := by linarith [(le_div_iff₀ hw1).mp hh]
  have hp := mul_nonneg (mul_nonneg hg hh') (sq_nonneg (z-r))
  have hid : (e+D-eh)*(e*r^2+D*z^2-eh*(r+omega*(z-r))^2-e*omega*(z-r)^2)-
      (e*r+D*z-eh*(r+omega*(z-r)))^2=
        (D-(e+D)*omega)*(e-eh*(1-omega))*(z-r)^2 := by ring
  have hd : (e*r+D*z-eh*(r+omega*(z-r)))^2/(e+D-eh)   ≤   
      e*r^2+D*z^2-eh*(r+omega*(z-r))^2-e*omega*(z-r)^2 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith
  linarith

theorem movement_chord_cost_bound {e D eh omega r z : ℝ}
    (he : 0 ≤ e) (hD : 0<D) (heh : 0 ≤ eh) (hw0 : 0 ≤ omega) (hw : omega<D/(e+D))
    (hh : eh ≤ e/(1-omega)) (hr : r ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ (e*r+D*z-eh*(r+omega*(z-r)))^2/(e+D-eh) ∧
      (e*r+D*z-eh*(r+omega*(z-r)))^2/(e+D-eh) ≤ e+D := by
  obtain ⟨hw1,ha⟩ := movement_strength_positive he hD hw0 hw hh
  have hA : 0<e+D := by linarith
  let theta := omega+(D-(e+D)*omega)/(e+D-eh)
  have hg : 0 ≤ D-(e+D)*omega := by linarith [(lt_div_iff₀ hA).mp hw]
  have htheta0 : 0 ≤ theta := add_nonneg hw0 (div_nonneg hg ha.le)
  have htheta1 : theta ≤ 1 := by
    have hh' := (le_div_iff₀ hw1).mp hh
    dsimp only [theta]
    have hd : (D-(e+D)*omega)/(e+D-eh) ≤ 1-omega := by
      apply (div_le_iff₀ ha).mpr
      nlinarith
    linarith
  have hrange : 0 ≤ (1-theta)*r+theta*z ∧ (1-theta)*r+theta*z ≤ 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) hr.1) (mul_nonneg htheta0 hz.1)
    · have h1 := mul_le_mul_of_nonneg_left hr.2 (by linarith : 0 ≤ 1-theta)
      have h2 := mul_le_mul_of_nonneg_left hz.2 htheta0
      nlinarith
  have heq : (e*r+D*z-eh*(r+omega*(z-r)))/(e+D-eh)=(1-theta)*r+theta*z := by
    dsimp only [theta]
    field_simp
    ring
  have hcost : (e*r+D*z-eh*(r+omega*(z-r)))^2/(e+D-eh)=
      (e+D-eh)*((e*r+D*z-eh*(r+omega*(z-r)))/(e+D-eh))^2 := by
    field_simp
  rw [hcost,heq]
  constructor
  · positivity
  · have hs : ((1-theta)*r+theta*z)^2 ≤ 1 := by nlinarith [hrange.1,hrange.2]
    have hm := mul_le_mul_of_nonneg_left hs ha.le
    nlinarith

theorem finite_parent_child_movement_gain
    (n : ℕ) (hn : 0<n) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (b h e r D z eh rhat omega : ℕ → ℝ) (err : ℝ)
    (he : ∀ j, 0  ≤  e j) (hD : ∀ j, 0<D j)
    (hw0 : ∀ j, 0  ≤  omega j) (hw : ∀ j, omega j<D j/(e j+D j))
    (hehat : ∀ j, eh j  ≤  e j/(1-omega j))
    (hrhat : ∀ j, rhat j=r j+omega j*(z j-r j))
    (hqb : Monotone (fun j => b j-e j-D j))
    (hqh : Monotone (fun j => h j+e j*r j+D j*z j))
    (htb : Monotone (fun j => b j-eh j))
    (hth : Monotone (fun j => h j+eh j*rhat j))
    (hqb0 : 0  ≤  b 0-e 0-D 0) (hqh0 : 0  ≤  h 0+e 0*r 0+D 0*z 0)
    (htb0 : 0  ≤  b 0-eh 0) (hth0 : 0  ≤  h 0+eh 0*rhat 0)
    (x : OrderedFeatureIndex n → ℝ)
    (hminimum : finiteCompensatedPressure n as b h e r x  ≤  
      finiteCompensatedPressure n as b h eh rhat x)
    (hchild : finiteCompensatedPressure n as (fun j => b j-e j) (fun j => h j+e j*r j) D z x  ≤  
      orderedSKPressure n as (fun j => b j-e j) (fun j => h j+e j*r j) x+err) :
    massStepSum as 0 (fun j => e j*omega j*(z j-r j)^2)  ≤  4*err := by
  have hpos (j : ℕ) := (movement_strength_positive (he j) (hD j) (hw0 j) (hw j) (hehat j)).2
  have hchord := orderedSK_cumulative_chord n hn as ha.pairwise ha.members_le_one
    (fun j => b j-e j-D j) (fun j => h j+e j*r j+D j*z j)
    (fun j => b j-eh j) (fun j => h j+eh j*rhat j)
    hqb hqh htb hth hqb0 hqh0 htb0 hth0
    (fun j _ => by linarith [hpos j]) (fun j _ hz => by exfalso; linarith [hpos j]) x
  have hcost (j : ℕ) :
      (h j+e j*r j+D j*z j-(h j+eh j*rhat j))^2/
        (b j-eh j-(b j-e j-D j))=
      (e j*r j+D j*z j-eh j*rhat j)^2/(e j+D j-eh j) := by
    congr 1 <;> ring
  simp_rw [hcost] at hchord
  have hsum : massStepSum as 0 (fun j => e j*omega j*(z j-r j)^2) ≤
      massStepSum as 0 (fun j => e j*(r j)^2+D j*(z j)^2-eh j*(rhat j)^2-
        (e j*r j+D j*z j-eh j*rhat j)^2/(e j+D j-eh j)) := massStepSum_mono as ha (fun j _ => by
    have hh := movement_pointwise_gain (r := r j) (z := z j)
      (he j) (hD j) (hw0 j) (hw j) (hehat j)
    rw [←hrhat j] at hh
    exact hh)
  have hadd : massStepSum as 0 (fun j => e j*(r j)^2+D j*(z j)^2)=
      massStepSum as 0 (fun j => e j*(r j)^2)+massStepSum as 0 (fun j => D j*(z j)^2) := by
    simpa only [one_mul] using massStepSum_linear as 0 1 1
      (fun j => e j*(r j)^2) (fun j => D j*(z j)^2)
  rw [massStepSum_sub,massStepSum_sub,hadd] at hsum
  unfold finiteCompensatedPressure at hminimum hchild
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
