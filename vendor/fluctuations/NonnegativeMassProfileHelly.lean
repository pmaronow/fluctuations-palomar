module

public import BoundedMassProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open Filter Set Function
open scoped Topology

def hellyCompression (x : ℝ) : ℝ := x/(1+x)

theorem hellyCompression_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hellyCompression x := by
  unfold hellyCompression
  positivity

theorem hellyCompression_lt_one {x : ℝ} (hx : 0 ≤ x) : hellyCompression x < 1 := by
  unfold hellyCompression
  apply (div_lt_iff₀ (by linarith : 0 < 1+x)).mpr
  linarith

theorem hellyCompression_monotoneOn : MonotoneOn hellyCompression (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold hellyCompression
  apply (div_le_div_iff₀ (by linarith : 0 < 1+x) (by linarith : 0 < 1+y)).mpr
  nlinarith

def NonnegativeMassProfile.hellyCompressed (a : NonnegativeMassProfile) : boundedMassProfiles :=
  ⟨fun x => hellyCompression (a.mass x),
    ⟨fun x => ⟨hellyCompression_nonneg (a.nonneg x),
      (hellyCompression_lt_one (a.nonneg x)).le⟩,
      fun x y hxy => hellyCompression_monotoneOn (a.nonneg x) (a.nonneg y) (a.monotone hxy)⟩⟩

theorem nonnegativeMassProfile_tendsto_subseq (u : ℕ → NonnegativeMassProfile)
    (hb : ∀ x : ℝ, ∃ C : ℝ, ∀ᶠ n in atTop, (u n).mass x ≤ C) :
    ∃ (a : NonnegativeMassProfile) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ x : ℝ, Tendsto (fun n => (u (φ n)).mass x) atTop (𝓝 (a.mass x)) := by
  classical
  obtain ⟨b, φ, hφ, ht⟩ := boundedMassProfiles_tendsto_subseq
    (fun n => (u n).hellyCompressed)
  have ht' (x : ℝ) : Tendsto (fun n => hellyCompression ((u (φ n)).mass x))
      atTop (𝓝 (b.val x)) :=
    tendsto_pi_nhds.mp (tendsto_subtype_rng.mp ht) x
  have hblt (x : ℝ) : b.val x < 1 := by
    obtain ⟨C, hC⟩ := hb x
    have hC0 : 0 ≤ C := by
      obtain ⟨n, hn⟩ := hC.exists
      exact (u n).nonneg x |>.trans hn
    have he := hφ.tendsto_atTop.eventually hC
    have hl : b.val x ≤ hellyCompression C :=
      le_of_tendsto (ht' x) (he.mono fun n hn =>
        hellyCompression_monotoneOn ((u (φ n)).nonneg x) hC0 hn)
    exact hl.trans_lt (hellyCompression_lt_one hC0)
  let a : NonnegativeMassProfile := {
    mass := fun x => b.val x/(1-b.val x)
    nonneg := fun x => div_nonneg (b.property.1 x).1 (sub_nonneg.mpr (hblt x).le)
    monotone := by
      intro x y hxy
      apply (div_le_div_iff₀ (by linarith [hblt x] : 0 < 1-b.val x)
        (by linarith [hblt y] : 0 < 1-b.val y)).mpr
      nlinarith [b.property.2 hxy] }
  refine ⟨a, φ, hφ, fun x => ?_⟩
  have hi := (ht' x).div (tendsto_const_nhds.sub (ht' x))
    (by linarith [hblt x] : (1:ℝ)-b.val x ≠ 0)
  convert hi using 1
  funext n
  change (u (φ n)).mass x = ((u (φ n)).mass x/(1+(u (φ n)).mass x))/
    (1-(u (φ n)).mass x/(1+(u (φ n)).mass x))
  have hpos : 0 < 1+(u (φ n)).mass x := by linarith [(u (φ n)).nonneg x]
  field_simp [hpos.ne']
  ring

theorem nonnegativeMassProfile_locallyBounded_tendsto_subseq
    (u : ℕ → NonnegativeMassProfile)
    (hb : ∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ n in atTop, (u n).mass R ≤ C) :
    ∃ (a : NonnegativeMassProfile) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ x : ℝ, Tendsto (fun n => (u (φ n)).mass x) atTop (𝓝 (a.mass x)) := by
  apply nonnegativeMassProfile_tendsto_subseq u
  intro x
  obtain ⟨C, hC⟩ := hb (max x 1) (lt_of_lt_of_le zero_lt_one (le_max_right x 1))
  exact ⟨C, hC.mono fun n hn => ((u n).monotone (le_max_left x 1)).trans hn⟩

end OAI.SKFluctuations.Hierarchy
