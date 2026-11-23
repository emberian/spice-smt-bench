import FixedPointTheorems.brouwer

namespace SpiceSmtBench

private theorem clamp_fixed {l h x r : ℝ} (lh : l ≤ h)
    (hl : x = l → r ≤ 0) (hh : x = h → 0 ≤ r)
    (hf : max l (min h (x-r)) = x) : r = 0 := by
  rcases le_total h (x-r) with hu | hu
  · rw [min_eq_left hu, max_eq_right lh] at hf
    linarith [hh hf.symm]
  · rw [min_eq_right hu] at hf
    rcases le_total l (x-r) with hd | hd
    · rw [max_eq_right hd] at hf; linarith
    · rw [max_eq_left hd] at hf; linarith [hl hf.symm]

/-- A continuous pair of residuals has a simultaneous zero if each component
has opposite weak signs on the two corresponding faces of a closed rectangle. -/
theorem rectangle_root (lo hi : ℝ × ℝ) (h : lo ≤ hi) (f : ℝ × ℝ → ℝ × ℝ)
    (hc : ContinuousOn f (Set.Icc lo hi))
    (left : ∀ x ∈ Set.Icc lo hi, x.1 = lo.1 → (f x).1 ≤ 0)
    (right : ∀ x ∈ Set.Icc lo hi, x.1 = hi.1 → 0 ≤ (f x).1)
    (bottom : ∀ x ∈ Set.Icc lo hi, x.2 = lo.2 → (f x).2 ≤ 0)
    (top : ∀ x ∈ Set.Icc lo hi, x.2 = hi.2 → 0 ≤ (f x).2) :
    ∃ x ∈ Set.Icc lo hi, f x = 0 := by
  let rect := Set.Icc lo hi
  let update (x : rect) : ℝ × ℝ :=
    (max lo.1 (min hi.1 (x.val.1-(f x.val).1)), max lo.2 (min hi.2 (x.val.2-(f x.val).2)))
  have hf : Continuous (fun x : rect => f x.val) := continuousOn_iff_continuous_domRestrict.mp hc
  have hu : Continuous update :=
    (continuous_const.max (continuous_const.min (continuous_subtype_val.fst.sub hf.fst))).prodMk
      (continuous_const.max (continuous_const.min (continuous_subtype_val.snd.sub hf.snd)))
  have inside (x : rect) : update x ∈ rect :=
    ⟨⟨le_max_left ..,le_max_left ..⟩,
     ⟨max_le h.1 (min_le_left ..),max_le h.2 (min_le_left ..)⟩⟩
  let g : C(rect,rect) := ⟨fun x => ⟨update x,inside x⟩, hu.subtype_mk inside⟩
  have cv : Convex ℝ rect := by
    rw [show rect = _ by exact Set.Icc_prod_eq lo hi]
    exact (convex_Icc ..).prod (convex_Icc ..)
  obtain ⟨x, fix⟩ := brouwer_fixed_point rect cv isCompact_Icc ⟨lo,le_rfl,h⟩ g
  have he := congrArg Subtype.val fix
  exact ⟨x.val, x.property, Prod.ext (clamp_fixed h.1 (left _ x.property) (right _ x.property) (congrArg Prod.fst he))
      (clamp_fixed h.2 (bottom _ x.property) (top _ x.property) (congrArg Prod.snd he))⟩

end SpiceSmtBench
