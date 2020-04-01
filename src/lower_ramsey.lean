import data.finset
import algebra.big_operators
import data.real.basic
import data.set.lattice

open finset
open nat

local notation `edges_of `X := powerset_len 2 X

universe u
variables {α : Type u} (G : finset α) {n : ℕ} [decidable_eq α]

lemma sum_const_nat {m : ℕ} {f : α → ℕ} {s : finset α} (h₁ : ∀x ∈ s, f x = m) :
  s.sum f = card s * m :=
begin
  rw [← nat.smul_eq_mul, ← sum_const],
  apply sum_congr rfl h₁
end

lemma exists_intermediate_set {A B : finset α} (i : ℕ)
  (h₁ : card A ≥ i + card B) (h₂ : B ⊆ A) :
  ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  rcases nat.le.dest h₁ with ⟨k, _⟩, clear h₁, revert A,
  induction k with k ih,
    intros A BsubA cards, exact ⟨A, BsubA, subset.refl _, cards.symm⟩,
  intros A BsubA cards,
  have: (A \ B).nonempty,
    rw [← card_pos, card_sdiff BsubA, ← cards, nat.add_right_comm, nat.add_sub_cancel, nat.add_succ],
    apply nat.succ_pos,
  rcases this with ⟨a, ha⟩,
  set A' := erase A a,
  have z: i + card B + k = card A',
    rw [card_erase_of_mem, ← cards, nat.add_succ, nat.pred_succ],
    rw mem_sdiff at ha, exact ha.1,
  rcases ih _ z with ⟨B', hB', B'subA', cards⟩,
  refine ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩,
  rintros t th, apply mem_erase_of_ne_of_mem _ (BsubA th), rintro rfl,
  rw mem_sdiff at ha, tauto
end

/-- We can shrink A to any smaller size. -/
lemma exists_smaller_set (A : finset α) (i : ℕ) (h₁ : card A ≥ i) :
  ∃ (B : finset α), B ⊆ A ∧ card B = i :=
begin
  rcases exists_intermediate_set i _ (empty_subset A) with ⟨B, _, x₁, x₂⟩,
  simp at x₂, exact ⟨B, x₁, x₂⟩, simpa,
end

def colourings : finset (finset (finset α)) := powerset (edges_of G)

lemma number_of_colourings (hn : card G = n) : card (colourings G) = 2^(choose n 2) :=
begin
  rw [colourings, card_powerset, card_powerset_len, hn]
end

def red_on (H : finset α) (c : finset (finset α)) : Prop := (edges_of H) ⊆ c

instance (H : finset α) : decidable_pred (red_on H) :=
begin
  intro,
  rw red_on,
  apply_instance
end

def blue_on (H : finset α) (c : finset (finset α)) : Prop := disjoint (edges_of H) c

instance (H : finset α) : decidable_pred (blue_on H) :=
begin
  intro,
  rw blue_on,
  rw disjoint_iff_inter_eq_empty,
  apply_instance
end

@[reducible]
def mono_on (H : finset α) (c : finset (finset α)) : Prop := red_on H c ∨ blue_on H c
-- instance (H : finset α) : decidable_pred (mono_on H) :=

lemma thing1 (hn : card G = n) {s : ℕ} (H : finset α) (HG : H ⊆ G) (hs : card H = s) :
  card ((colourings G).filter (blue_on H)) = 2^(choose n 2 - choose s 2) :=
begin
  have: filter (blue_on H) (colourings G) = powerset ((edges_of G) \ (edges_of H)),
    ext c, rw [mem_filter, colourings, mem_powerset, mem_powerset, blue_on, disjoint_right, subset_iff, subset_iff, ← ball_and_distrib], simp,
  rw this,
  rw card_powerset,
  congr' 1,
  rw [card_sdiff, card_powerset_len, card_powerset_len, hn, hs],
  apply powerset_len_mono HG
end

lemma thing2 (H : finset α) (HG : H ⊆ G) : card ((colourings G).filter (red_on H)) = card ((colourings G).filter (blue_on H)) :=
begin
  let f : finset (finset α) → finset (finset α) := λ c, c ∪ edges_of H,
  have : card (image f ((colourings G).filter (blue_on H))) = card ((colourings G).filter (blue_on H)),
  { apply card_image_of_inj_on,
    simp only [mem_filter],
    rintros c₁ ⟨hc₁₁, hc₁₂⟩ c₂ ⟨hc₂₁, hc₂₂⟩ h,
    ext e,
    by_cases z: e ∈ edges_of H,
      rw [blue_on, disjoint_left] at hc₁₂ hc₂₂,
      simp [hc₁₂ z, hc₂₂ z],
    split,
      intro he,
      have q: e ∈ f c₁, apply subset_union_left, apply he,
      rw [h, mem_union] at q,
      apply q.resolve_right z,
    intro he,
    have q: e ∈ f c₂, apply subset_union_left, apply he,
    rw [← h, mem_union] at q,
    apply q.resolve_right z,
  },
  rw ← this,
  congr' 1,
  ext c,
  simp [colourings],
  split,
    rintro ⟨ha₁, ha₂⟩,
    use c \ edges_of H,
    rw [subset_iff, blue_on, disjoint_right, ← ball_and_distrib],
    simp only [mem_sdiff],
    refine ⟨λ e, _, _⟩,
      rintro ⟨t, _⟩,
      refine ⟨ha₁ t, ‹_›⟩,
    apply sdiff_union_of_subset ha₂,
  rintro ⟨c', ⟨⟨h₁, h₂⟩, rfl⟩⟩,
  refine ⟨_, _⟩,
    apply union_subset h₁,
    apply powerset_len_mono HG,
  apply subset_union_right
end

lemma thing3 (hn : card G = n) {s : ℕ} (H : finset α) (HG : H ⊆ G) (hs : card H = s) (h2s : 2 ≤ s):
  card ((colourings G).filter (mono_on H)) = 2 * 2^(choose n 2 - choose s 2) :=
begin
  rw filter_or,
  rw card_disjoint_union,
  rw thing2,
  rw ← two_mul,
  rw thing1,
  apply hn,
  apply HG,
  apply hs,
  apply HG,
  rw disjoint_left,
  intro c,
  simp only [red_on, blue_on, and_imp, filter_congr_decidable, mem_filter, not_and],
  intros _ _ _ _,
  have: disjoint (powerset_len 2 H) (powerset_len 2 H),
    apply disjoint_of_subset_right,
    apply a_1,
    apply a_3,
  rw disjoint_self at this,
  rcases exists_smaller_set H 2 _ with ⟨e, he⟩,
    revert this,
    apply ne_empty_of_mem,
    rw mem_powerset_len,
    exact he,
  rw hs,
  exact h2s
end

@[reducible]
def has_mono (G : finset α) (s : ℕ) (c : finset (finset α)) : Prop := ∃ (H' ∈ powerset_len s G), mono_on H' c

lemma card_filter_bex {β : Type*} (A : finset α) (B : finset β) (p : α → β → Prop) [∀ a x, decidable (p a x)] :
  card (A.filter (λ a, ∃ x ∈ B, p a x)) ≤ B.sum (λ x, card (A.filter (λ a, p a x))) :=
begin
  apply le_trans _ card_bind_le,
  apply_instance,
  apply card_le_of_subset,
  intro a,
  simp,
  intros,
  use x,
  tauto
end

lemma thing4 (s : ℕ) (hn : card G = n) (hs : 2 ≤ s):
  card ((colourings G).filter (has_mono G s)) ≤ choose n s * 2 * 2^(choose n 2 - choose s 2) :=
begin
  apply le_trans (card_filter_bex _ _ _),
  rw sum_const_nat,
  rw card_powerset_len,
  rw hn,
  rw ← mul_assoc,
  simp only [mem_powerset_len],
  intros H HG, apply thing3 _ hn, tauto, tauto, assumption,
  apply_instance
end

lemma thing5 {s : ℕ} (small : ↑n < (sqrt 2)^(s-1)) : choose n s * 2 * 2^(choose n 2 - choose s 2) < 2^(choose n 2) :=
sorry
-- idea: suffices to show
-- choose n s * 2 * 2^(- choose s 2) < 1, ie
-- choose n s * 2 < 2^(choose s 2)
-- so it's good enough to show
-- n^s < 2^(s*(s-1)/2), ie
-- n < 2^((s-1)/2), which is just our assumption


local attribute [instance] classical.prop_decidable

theorem lower_ramsey (G : finset α) {n : ℕ} {s : ℕ} (hs : 2 ≤ s) (small : ↑n < (sqrt 2)^(s-1)) (hn : card G = n) :
  ∃ (c : finset (finset α)), ¬ has_mono G s c :=
begin
  by_contra,
  push_neg at a,
  have: card (filter (has_mono G s) (colourings G)) = card (colourings G),
    congr' 1,
    convert filter_true,
      ext, rw [iff_true], apply a,
    apply_instance,
  rw [number_of_colourings _ hn] at this,
  revert this,
  apply ne_of_lt,
  apply lt_of_le_of_lt _ (thing5 small),
  convert thing4 G s hn hs,
end