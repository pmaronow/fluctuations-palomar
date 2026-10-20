module

public import WallSampledFieldGap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization

theorem wallDyadicBand_cost_algebra {M mesh N g s v : ℝ}
    (hM : 0 ≤ M) (hmesh : 0 ≤ mesh) (hN : 0 < N) (hg : 0 < g)
    (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s) :
    let H := 2*M/(N*g)+2*mesh*M
    (v/2)*(4*M^2+(112/3:ℝ)*(v/4)⁻¹^2*(2*H/s))+2*H/(s/2)^2 ≤
      2*v*M^2+1300*M/(N*g*s*v)+1300*mesh*M/(s*v) := by
  dsimp only
  let H := 2*M/(N*g)+2*mesh*M
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hwin : (v/2)*(4*M^2+(112/3:ℝ)*(v/4)⁻¹^2*(2*H/s)) =
      2*v*M^2+(1792/3:ℝ)*H/(s*v) := by
    field_simp
    ring
  have hcov : 2*H/(s/2)^2 ≤ 8*H/(s*v) := by
    have hden : 0 < s*v := mul_pos hs hv
    have hss : 0 < (s/2)^2 := sq_pos_of_pos (by positivity)
    apply (div_le_div_iff₀ hss hden).mpr
    nlinarith [mul_nonneg hH (sub_nonneg.mpr hvs)]
  have hr : (1792/3:ℝ)*H/(s*v)+8*H/(s*v) ≤650*H/(s*v) := by
    rw [← add_div]
    apply (div_le_div_iff₀ (mul_pos hs hv) (mul_pos hs hv)).mpr
    nlinarith [mul_nonneg hH (mul_pos hs hv).le]
  calc
    _ = 2*v*M^2+(1792/3:ℝ)*H/(s*v)+2*H/(s/2)^2 := by rw [hwin]
    _ ≤ 2*v*M^2+650*H/(s*v) := by linarith
    _ = _ := by dsimp [H]; ring

theorem wallDyadicBand_wallSlope_algebra {T ε θ d rmin s v M mesh : ℝ} {n : ℕ}
    (hM : 0 ≤ M) (hmesh : 0 ≤ mesh) (hn : 0 < (n:ℝ))
    (hε : ε ∈ Set.Ioo 0 T) (hθ : 0 < θ) (hd : d ≠ 0)
    (hrmin : 0 < rmin) (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s)
    (hlogn : 0 < Real.log (n:ℝ)) :
    let H := 2*M/((n:ℝ)*wallBandSlope T ε θ d rmin v n)+2*mesh*M
    (v/2)*(4*M^2+(112/3:ℝ)*(v/4)⁻¹^2*(2*H/s))+2*H/(s/2)^2 ≤
      2*v*M^2+28600*M*Real.log (n:ℝ)/
        ((n:ℝ)*θ*wallLowStrength T ε*wallLowRadius d rmin ε*s)+1300*mesh*M/(s*v) := by
  have hg := wallBandSlope_pos hε hθ hd hrmin hv hlogn
  have h := wallDyadicBand_cost_algebra hM hmesh hn hg hs hv hvs
  dsimp only at h ⊢
  have heq : 1300*M/((n:ℝ)*wallBandSlope T ε θ d rmin v n*s*v) =
      28600*M*Real.log (n:ℝ)/
        ((n:ℝ)*θ*wallLowStrength T ε*wallLowRadius d rmin ε*s) := by
    unfold wallBandSlope
    field_simp
    ring
  rwa [heq] at h

theorem wallDyadicBand_actualMass_cost_algebra {M mesh N g s v : ℝ}
    (hM : 0 ≤ M) (hmesh : 0 ≤ mesh) (hN : 0 < N) (hg : 0 < g)
    (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s/2) :
    let H := 2*M/(N*g)+2*mesh*M
    (v/2)*(4*M^2+(112/3:ℝ)*(v/4)⁻¹^2*(H/(s-v)))+2*H/(s-v)^2 ≤
      2*v*M^2+1300*M/(N*g*s*v)+1300*mesh*M/(s*v) := by
  dsimp only
  let H := 2*M/(N*g)+2*mesh*M
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hhalf : s/2 ≤ s-v := by linarith
  have hsv : 0 < s-v := (by positivity : 0 < s/2).trans_le hhalf
  have hW : H/(s-v) ≤ 2*H/s := by
    have h := div_le_div_of_nonneg_left hH (by positivity : 0 < s/2) hhalf
    have he : H/(s/2)=2*H/s := by ring
    rwa [he] at h
  have hC : 2*H/(s-v)^2 ≤ 2*H/(s/2)^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (by positivity))
    nlinarith
  have hco : 0 ≤ (112/3:ℝ)*(v/4)⁻¹^2 := by positivity
  have hW' := mul_le_mul_of_nonneg_left hW hco
  have hW'' := mul_le_mul_of_nonneg_left (add_le_add (le_rfl : 4*M^2 ≤ 4*M^2) hW') (by positivity : 0 ≤ v/2)
  calc
    _ ≤ (v/2)*(4*M^2+(112/3:ℝ)*(v/4)⁻¹^2*(2*H/s))+2*H/(s/2)^2 :=
      add_le_add hW'' hC
    _ ≤ _ := wallDyadicBand_cost_algebra hM hmesh hN hg hs hv (by linarith)

end OAI.SKFluctuations.LaplaceWindowFormalization
