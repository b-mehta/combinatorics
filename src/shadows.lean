import data.finset
import data.fintype
import to_mathlib
import basic

open fintype
open finset
open nat

variables {α : Type*} [decidable_eq α] 

def example1 : finset (finset (fin 5)) :=
{ {0,1,2}, {0,1,3}, {0,2,3}, {0,2,4} } 

section shadow
  def all_removals (A : finset α) : finset (finset α) := A.image (erase A)

  lemma all_removals_size {A : finset α} {r : ℕ} (h : A.card = r) : is_layer (all_removals A) (r-1) := 
  begin
    intros B H,
    rw [all_removals, mem_image] at H,
    rcases H with ⟨i, ih, Bh⟩,
    rw [← Bh, card_erase_of_mem ih, h], refl
  end

  lemma mem_all_removals {A : finset α} {B : finset α} : B ∈ all_removals A ↔ ∃ i ∈ A, erase A i = B :=
  by simp only [all_removals, mem_image]

  lemma card_all_removals {A : finset α} {r : ℕ} (H : card A = r) : (all_removals A).card = r :=
  begin
    rwa [all_removals, card_image_of_inj_on],
    intros i ih j _ k,
    have q: i ∉ erase A j := k ▸ not_mem_erase i A,
    rw [mem_erase, not_and] at q,
    by_contra a, apply q a ih
  end

  def shadow (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.bind all_removals

  reserve prefix `∂`:90
  notation ∂𝒜 := shadow 𝒜

  lemma mem_shadow {𝒜 : finset (finset α)} (B : finset α) : B ∈ shadow 𝒜 ↔ ∃ A ∈ 𝒜, ∃ i ∈ A, erase A i = B := 
  by simp only [shadow, all_removals, mem_bind, mem_image]

  lemma mem_shadow' {𝒜 : finset (finset α)} {B : finset α} : B ∈ shadow 𝒜 ↔ ∃ j ∉ B, insert j B ∈ 𝒜 :=
  begin
    rw mem_shadow,
    split,
      rintro ⟨A, HA, i, Hi, k⟩,
      rw ← k,
      refine ⟨i, not_mem_erase i A, _⟩,
      rwa insert_erase Hi,
    rintro ⟨i, Hi, k⟩,
      refine ⟨insert i B, k, i, mem_insert_self _ _, _⟩,
      rw erase_insert Hi
  end

  lemma shadow_layer {𝒜 : finset (finset α)} {r : ℕ} : is_layer 𝒜 r → is_layer (∂𝒜) (r-1) :=
  begin
    intros a A H,
    rw [shadow, mem_bind] at H,
    rcases H with ⟨B, _, _⟩,
    exact all_removals_size (a _ ‹_›) _ ‹A ∈ all_removals B›,
  end

  lemma sub_iff_shadow_one {𝒜 : finset (finset α)} {B : finset α} : B ∈ ∂𝒜 ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ card (A \ B) = 1 :=
  begin
    rw mem_shadow', split, 
      rintro ⟨i, ih, inA⟩,
      refine ⟨insert i B, inA, subset_insert _ _, _⟩, rw card_sdiff (subset_insert _ _), simp [card_insert_of_not_mem ih],
    rintro ⟨A, hA, _⟩,
    rw card_eq_one at a_h_h, rcases a_h_h with ⟨subs, j, eq⟩, 
    use j, refine ⟨_, _⟩, 
    intro, have: j ∈ finset.singleton j, rw mem_singleton, rw ← eq at this, rw mem_sdiff at this, exact this.2 a, 
    rw ← union_singleton_eq_insert, rw ← eq, rwa sdiff_union_of_subset subs, 
  end

  lemma sub_of_shadow {𝒜 : finset (finset α)} {B : finset α} : B ∈ ∂𝒜 → ∃ A ∈ 𝒜, B ⊆ A :=
  by rw sub_iff_shadow_one; tauto

  lemma sub_iff_shadow_iter {𝒜 : finset (finset α)} {B : finset α} (k : ℕ) : 
    B ∈ (shadow^[k] 𝒜) ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ card (A \ B) = k :=
  begin
    revert 𝒜 B,
    induction k with k ih,
      simp, intros 𝒜 B, 
      split,
        intro p, refine ⟨B, p, subset.refl _, _⟩, apply eq_empty_of_forall_not_mem, intro x, rw mem_sdiff, tauto,
      rintro ⟨A, _, _⟩, rw sdiff_eq_empty_iff_subset at a_h_right, have: A = B := subset.antisymm a_h_right.2 a_h_right.1,
      rwa ← this,
    simp, intros 𝒜 B, have := @ih (∂𝒜) B,
    rw this, clear this ih,
    split, 
      rintro ⟨A, hA, BsubA, card_AdiffB_is_k⟩, rw sub_iff_shadow_one at hA, rcases hA with ⟨C, CinA, AsubC, card_CdiffA_is_1⟩,
      refine ⟨C, CinA, trans BsubA AsubC, _⟩,
      rw card_sdiff (trans BsubA AsubC), rw card_sdiff BsubA at card_AdiffB_is_k, rw card_sdiff AsubC at card_CdiffA_is_1,
      by calc card C - card B = (card C - card A + card A) - card B : begin rw nat.sub_add_cancel, apply card_le_of_subset AsubC end 
      ... = (card C - card A) + (card A - card B) : begin rw nat.add_sub_assoc, apply card_le_of_subset BsubA end
      ... = k + 1 : begin rw [card_CdiffA_is_1, card_AdiffB_is_k, add_comm] end,
    rintro ⟨A, hA, _, _⟩, 
    have z: A \ B ≠ ∅, rw ← card_pos, rw a_h_right_right, exact nat.succ_pos _,
    rw [ne, ← exists_mem_iff_ne_empty] at z, 
    rcases z with ⟨i, hi⟩,
    have: i ∈ A, rw mem_sdiff at hi, exact hi.1,
    have: B ⊆ erase A i, { intros t th, apply mem_erase_of_ne_of_mem _ (a_h_right_left th), intro, rw mem_sdiff at hi, rw a at th, exact hi.2 th },
    refine ⟨erase A i, _, ‹_›, _⟩,
    { rw mem_shadow, refine ⟨A, hA, i, ‹_›, rfl⟩ }, 
    rw card_sdiff ‹B ⊆ erase A i›, rw card_erase_of_mem ‹i ∈ A›, rw nat.pred_sub, rw ← card_sdiff a_h_right_left, rw a_h_right_right, simp,
  end
end shadow

#eval example1
#eval shadow example1

section local_lym
  lemma multiply_out {A B n r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ n)
    (h : A * r ≤ B * (n - r + 1)) : (A : ℚ) / (nat.choose n r) ≤ B / nat.choose n (r-1) :=
  begin
    rw div_le_div_iff; norm_cast,
    apply le_of_mul_le_mul_right _ ‹0 < r›,
    cases r,
      simp,
    rw nat.succ_eq_add_one at *,
    rw [← nat.sub_add_comm hr2, nat.add_sub_add_right] at h,
    convert nat.mul_le_mul_right (choose n r) h using 1;
      {simp [mul_assoc, nat.choose_succ_right_eq], ac_refl},
    apply nat.choose_pos hr2,
    apply nat.choose_pos (le_trans (nat.pred_le _) hr2)
  end

  def the_pairs (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
  𝒜.bind (λ A, (all_removals A).image (prod.mk A))

  lemma card_the_pairs {r : ℕ} (𝒜 : finset (finset α)) : is_layer 𝒜 r → (the_pairs 𝒜).card = 𝒜.card * r :=
  begin
    intro, rw [the_pairs, card_bind],
    { convert (sum_congr rfl _),
      { rw [← nat.smul_eq_mul, ← sum_const] }, 
      intros,
      rw [card_image_of_inj_on, card_all_removals (a _ H)],
      exact (λ _ _ _ _ k, (prod.mk.inj k).2) },
    simp only [disjoint_left, mem_image],
    rintros _ _ _ _ k a ⟨_, _, rfl⟩ ⟨_, _, a₂⟩,
    exact k (prod.mk.inj a₂.symm).1,
  end

  def from_below [fintype α] (𝒜 : finset (finset α)) : finset (finset α × finset α) :=
  (∂𝒜).bind (λ B, (univ \ B).image (λ x, (insert x B, B)))

  lemma mem_the_pairs {𝒜 : finset (finset α)} (A B : finset α) : (A,B) ∈ the_pairs 𝒜 ↔ A ∈ 𝒜 ∧ B ∈ all_removals A :=
  begin
    simp only [the_pairs, mem_bind, mem_image],
    split, 
    { rintro ⟨a, Ha, b, Hb, h⟩, 
      rw [(prod.mk.inj h).1, (prod.mk.inj h).2] at *,
      exact ⟨Ha, Hb⟩ },
    { intro h, exact ⟨A, h.1, B, h.2, rfl⟩}
  end

  lemma mem_from_below [fintype α] {𝒜 : finset (finset α)} (A B : finset α) : A ∈ 𝒜 ∧ (∃ (i ∉ B), insert i B = A) → (A,B) ∈ from_below 𝒜 :=
  begin
    rw [from_below, mem_bind],
    rintro ⟨Ah, i, ih, a⟩,
    refine ⟨B, _, _⟩,
      rw mem_shadow',
      refine ⟨i, ih, a.symm ▸ Ah⟩,
    rw mem_image,
    exact ⟨i, mem_sdiff.2 ⟨complete _, ih⟩, by rw a⟩,
  end

  lemma above_sub_below [fintype α] (𝒜 : finset (finset α)) : the_pairs 𝒜 ⊆ from_below 𝒜 :=
  begin
    rintros ⟨A,B⟩ h,
    rw [mem_the_pairs, mem_all_removals] at h,
    apply mem_from_below,
    rcases h with ⟨Ah, i, ih, AeB⟩,
    refine ⟨Ah, i, _, _⟩; rw ← AeB,
      apply not_mem_erase,
    apply insert_erase ih
  end

  lemma card_from_below [fintype α] {𝒜 : finset (finset α)} (r : ℕ) : is_layer 𝒜 r → (from_below 𝒜).card ≤ (∂𝒜).card * (card α - (r - 1)) :=
  begin
    intro,
    rw [from_below],
    convert card_bind_le,
    rw [← nat.smul_eq_mul, ← sum_const],
    apply sum_congr rfl,
    intros, 
    rw [card_image_of_inj_on, card_univ_diff, shadow_layer a _ H],
    intros x1 x1h _ _ h,
    have q := mem_insert_self x1 x, 
    rw [(prod.mk.inj h).1, mem_insert] at q,
    apply or.resolve_right q ((mem_sdiff.1 x1h).2),
  end

  -- generalise this: can remove hr2 and possibly hr1
  theorem local_lym [fintype α] {𝒜 : finset (finset α)} {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ card α) (H : is_layer 𝒜 r):
    (𝒜.card : ℚ) / nat.choose (card α) r ≤ (∂𝒜).card / nat.choose (card α) (r-1) :=
  begin
    apply multiply_out hr1 hr2,
    rw ← card_the_pairs _ H,
    transitivity,
      apply card_le_of_subset (above_sub_below 𝒜),
    rw ← nat.sub_sub_assoc hr2 hr1,
    apply card_from_below _ H
  end
end local_lym

section slice
  def slice (𝒜 : finset (finset α)) (r : ℕ) : finset (finset α) := 𝒜.filter (λ i, card i = r)

  reserve infix `#`:100
  notation 𝒜#r := slice 𝒜 r

  lemma mem_slice {𝒜 : finset (finset α)} {r : ℕ} {A : finset α} : A ∈ 𝒜#r ↔ A ∈ 𝒜 ∧ A.card = r :=
  by rw [slice, mem_filter]

  lemma layered_slice {𝒜 : finset (finset α)} {r : ℕ} : is_layer (𝒜#r) r := λ _ h, (mem_slice.1 h).2

  lemma ne_of_diff_slice {𝒜 : finset (finset α)} {r₁ r₂ : ℕ} {A₁ A₂ : finset α} (h₁ : A₁ ∈ 𝒜#r₁) (h₂ : A₂ ∈ 𝒜#r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
  mt (λ h, (layered_slice A₁ h₁).symm.trans ((congr_arg card h).trans (layered_slice A₂ h₂)))
end slice

section lym
  def antichain (𝒜 : finset (finset α)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ¬(A ⊆ B)

  def decompose' [fintype α] (𝒜 : finset (finset α)) : Π (k : ℕ), finset (finset α)
    | 0 := 𝒜#(card α)
    | (k+1) := 𝒜#(card α - (k+1)) ∪ shadow (decompose' k)

  lemma decompose'_layer [fintype α] (𝒜 : finset (finset α)) (k : ℕ) : is_layer (decompose' 𝒜 k) (card α - k) :=
  begin
    induction k with k ih;
      rw decompose',
      apply layered_slice,
    rw ← union_layer,
    split,
      apply layered_slice,
    apply shadow_layer ih,
  end

  theorem antichain_prop [fintype α] {𝒜 : finset (finset α)} {r k : ℕ} (hk : k ≤ card α) (hr : r < k) (H : antichain 𝒜) :
  ∀ A ∈ 𝒜#(card α - k), ∀ B ∈ ∂decompose' 𝒜 r, ¬(A ⊆ B) :=
  begin
    intros A HA B HB k,
    rcases sub_of_shadow HB with ⟨C, HC, _⟩,
    replace k := trans k ‹B ⊆ C›, clear HB h_h B,
    induction r with r ih generalizing A C;
    rw decompose' at HC,
    any_goals { rw mem_union at HC, cases HC },
    any_goals { refine H A (mem_slice.1 HA).1 C (mem_slice.1 HC).1 _ ‹A ⊆ C›,
                apply ne_of_diff_slice HA HC _,
                apply ne_of_lt },
    { apply nat.sub_lt_of_pos_le _ _ hr hk },
    { mono },
    obtain ⟨_, HB', HB''⟩ := sub_of_shadow HC,
    refine ih (nat.lt_of_succ_lt hr) _ _ HA HB' (trans k_1 HB'')
  end

  lemma disjoint_of_antichain [fintype α] {𝒜 : finset (finset α)} {k : ℕ} (hk : k + 1 ≤ card α) (H : antichain 𝒜) : 
    disjoint (𝒜#(card α - (k + 1))) (∂decompose' 𝒜 k) := 
  disjoint_left.2 $ λ A HA HB, antichain_prop hk (lt_add_one k) H A HA A HB (subset.refl _)

  lemma card_decompose'_other [fintype α] {𝒜 : finset (finset α)} {k : ℕ} (hk : k ≤ card α) (H : antichain 𝒜) : 
    sum (range (k+1)) (λ r, ((𝒜#(card α - r)).card : ℚ) / nat.choose (card α) (card α - r)) ≤ ((decompose' 𝒜 k).card : ℚ) / nat.choose (card α) (card α-k) :=
  begin
    induction k with k ih,
      rw [sum_range_one, div_le_div_iff]; norm_cast, exact nat.choose_pos (nat.sub_le _ _), exact nat.choose_pos (nat.sub_le _ _),
    rw [sum_range_succ, decompose'],
    have: (𝒜#(card α - (k + 1)) ∪ ∂decompose' 𝒜 k).card = (𝒜#(card α - (k + 1))).card + (∂decompose' 𝒜 k).card,
      apply card_disjoint_union,
      rw disjoint_iff_ne,
      intros A hA B hB m,
      apply antichain_prop hk (lt_add_one k) H A hA B hB,
      rw m, refl,
    rw this,
    have: ↑((𝒜#(card α - (k + 1))).card + (∂decompose' 𝒜 k).card) / (nat.choose (card α) (card α - nat.succ k) : ℚ) = 
          ((𝒜#(card α - (k + 1))).card : ℚ) / (nat.choose (card α) (card α - nat.succ k)) + ((∂decompose' 𝒜 k).card : ℚ) / (nat.choose (card α) ((card α) - nat.succ k)),
      rw ← add_div,
      norm_cast,
    rw this,
    apply add_le_add_left,
    transitivity,
      exact ih (le_of_lt hk),
    apply local_lym (nat.le_sub_left_of_add_le hk) (nat.sub_le _ _) (decompose'_layer _ _)
  end

  lemma card_decompose_other [fintype α] {𝒜 : finset (finset α)} (H : antichain 𝒜) : 
    (range (card α + 1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose (card α) r) ≤ (decompose' 𝒜 (card α)).card / nat.choose (card α) 0 :=
  begin
    rw [← nat.sub_self (card α)],
    convert ← card_decompose'_other (le_refl _) H using 1,
    apply sum_flip (λ r, ((𝒜#r).card : ℚ) / nat.choose (card α) r), 
  end

  lemma lubell_yamamoto_meshalkin [fintype α] {𝒜 : finset (finset α)} (H : antichain 𝒜) : 
    (range (card α + 1)).sum (λ r, ((𝒜#r).card : ℚ) / nat.choose (card α) r) ≤ 1 :=
  begin
    transitivity,
      apply card_decompose_other H,
    rw div_le_iff; norm_cast,
      simpa only [mul_one, nat.choose_zero_right, nat.sub_self] using size_in_layer (decompose'_layer 𝒜 (card α)),
    apply nat.choose_pos (nat.zero_le _)
  end
end lym