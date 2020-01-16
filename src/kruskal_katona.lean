/- 
The Kruskal-Katona theorem in a few different versions, and an application to the Erdos-Ko-Rado theorem.
-/

import algebra.geom_sum
import data.finset
import data.fintype
import tactic
import to_mathlib
import basic
import shadows
import colex
import compressions.UV

open fintype
open finset
open nat

variable {α : Type*}
variables {n : ℕ}

namespace UV
section 
  -- Applying the compression makes the set smaller in colex
  -- This is intuitive since a portion of the set is being shifted 'down' 
  -- as max U < max V
  lemma compression_reduces_set [decidable_linear_order α] {U V : finset α} {hU : U ≠ ∅} {hV : V ≠ ∅} (A : finset α) (h : max' U hU < max' V hV): 
    compress U V A ≠ A → compress U V A <ᶜ A :=
  begin
    rw compress, split_ifs with h₁; intro h₂, any_goals {exfalso, apply h₂, refl}, 
    refine ⟨max' V hV, _, not_mem_sdiff_of_mem_right (max'_mem _ _), h₁.2 (max'_mem _ _)⟩, 
    intros x hx, 
    have xV: x ∉ V := λ z, not_le_of_lt hx (le_max' _ _ _ z),
    have xU: x ∉ U := λ z, not_le_of_lt hx (trans (le_max' _ _ _ z) (le_of_lt h)), 
    simp [xU, xV]
  end

  lemma binary_sum_nat {k : ℕ} {A : finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) : A.sum (pow 2) < 2^k :=
  begin
    apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t, mem_range.2 ∘ h₁)),
    have z := geom_sum_mul_add 1 k, rw [geom_series, mul_one] at z, 
    simp only [nat.pow_eq_pow] at z, rw ← z, apply nat.lt_succ_self
  end

  -- We have an equivalent relation to the colex order, for subsets of ℕ.
  -- Note this gives a proof that <ᶜ is decidable for α = ℕ, which we didn't have before.
  lemma binary_iff (A B : finset ℕ) : A.sum (pow 2) < B.sum (pow 2) ↔ A <ᶜ B :=
  begin
    have z: ∀ (A B : finset ℕ), A <ᶜ B → A.sum (pow 2) < B.sum (pow 2),
      rintro A B ⟨k, maxi, notinA, inB⟩,
      have AeqB: A.filter (λ x, ¬(x ≤ k)) = B.filter (λ x, ¬(x ≤ k)),
      { ext t, by_cases h: (k < t); simp [h], apply maxi h },
      have Alt: (A.filter (λ x, x ≤ k)).sum (pow 2) < pow 2 k :=
        binary_sum_nat (λ _, (λ th, lt_of_le_of_ne (and.right th) (ne_of_mem_of_not_mem th.left notinA)) ∘ mem_filter.1), 
      have leB: pow 2 k ≤ (B.filter (λ x, x ≤ k)).sum (pow 2),
      { apply single_le_sum (λ _ _, nat.zero_le _) (mem_filter.2 ⟨inB, _⟩), refl },
      have := add_lt_add_right (lt_of_lt_of_le Alt leB) ((filter (λ x, ¬(x ≤ k)) A).sum (pow 2)),
      rwa [← sum_union, filter_union_filter_neg_eq, AeqB, ← sum_union, filter_union_filter_neg_eq] at this, 
      any_goals { rw disjoint_iff_inter_eq_empty, apply filter_inter_filter_neg_eq },
    refine ⟨λ h, (trichotomous A B).resolve_right (λ h₁, h₁.elim _ (λ q, not_lt_of_gt h (z _ _ q))), z A B⟩, 
    rintro rfl, apply irrefl _ h
  end
  -- This measures roughly how much we've compressed the family 
  def family_measure_fin (𝒜 : finset (finset (fin n))) : ℕ := 𝒜.sum (λ A, (A.image fin.val).sum (pow 2))

  -- Applying a compression strictly decreases the measure
  lemma compression_reduces_family {U V : finset (fin n)} {hU : U ≠ ∅} {hV : V ≠ ∅} (h : max' U hU < max' V hV) (𝒜 : finset (finset (fin n))) : 
    compress_family U V 𝒜 ≠ 𝒜 → family_measure_fin (compress_family U V 𝒜) < family_measure_fin 𝒜 :=
  begin
    rw [compress_family], 
    have q: ∀ Q ∈ filter (λ A, compress U V A ∉ 𝒜) 𝒜, compress U V Q ≠ Q,
      intros Q HQ, rw mem_filter at HQ, apply (ne_of_mem_of_not_mem HQ.1 HQ.2).symm, 
    intro,
    set CA₁ := filter (λ A, compress U V A ∈ 𝒜) 𝒜,
    have uA: CA₁ ∪ filter (λ A, compress U V A ∉ 𝒜) 𝒜 = 𝒜 := filter_union_filter_neg_eq _, 
    have ne₂: filter (λ A, compress U V A ∉ 𝒜) 𝒜 ≠ ∅, intro z, rw [compress_motion, z, image_empty, empty_union] at a, rw [z, union_empty] at uA, exact a uA,
    rw [family_measure_fin, family_measure_fin, sum_union (compress_disjoint U V)], 
    conv_rhs {rw ← uA}, 
    rw [sum_union, add_comm, add_lt_add_iff_left, sum_image], 
    apply sum_lt_sum ne₂, 
    intros A hA, 
    rw binary_iff, 
    rw colex_hom_fin,
    apply compression_reduces_set A h (q _ hA), 
    intros x Hx y Hy k,
    have cx := q x Hx, 
    have cy := q y Hy, 
    rw compress at k cx, split_ifs at k cx, 
      rw compress at k cy, split_ifs at k cy,
        exact inj_ish h_1 h_2 k, 
      exfalso, apply cy rfl,
    exfalso, apply cx rfl, 
    rw disjoint_iff_inter_eq_empty,
    apply filter_inter_filter_neg_eq
  end

  -- These are the compressions which decrease the "measure" of a family of sets
  def useful_compression [decidable_linear_order α] : rel (finset α) (finset α) := (λ U V, ∃ (HU : U ≠ ∅), ∃ (HV : V ≠ ∅), disjoint U V ∧ finset.card U = finset.card V ∧ max' U HU < max' V HV)

  -- Applying the right compression will decrease measure, keep cardinality, keep sizes and decrease shadow
  lemma compression_improved {r : ℕ} (U V : finset (fin n)) (𝒜 : finset (finset (fin n))) (h : all_sized 𝒜 r) (h₁ : useful_compression U V) 
    (h₂ : ∀ U₁ V₁, useful_compression U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ 𝒜) (h₃ : ¬ is_compressed U V 𝒜): 
    family_measure_fin (compress_family U V 𝒜) < family_measure_fin 𝒜 ∧ (compress_family U V 𝒜).card = 𝒜.card ∧ all_sized (compress_family U V 𝒜) r ∧ (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := 
  begin
    rcases h₁ with ⟨Uh, Vh, UVd, same_size, max_lt⟩,
    refine ⟨compression_reduces_family max_lt _ h₃, compressed_size _ _, _, _⟩,
    apply compress_family_size _ _ _ _ same_size h, 
    apply compression_reduces_shadow _ same_size,
    intros x Hx, refine ⟨min' V Vh, min'_mem _ _, _⟩,
    cases lt_or_le 1 U.card with p p,
    { apply h₂,
      refine ⟨⟨_, _, _, _, _⟩, card_erase_lt_of_mem Hx⟩,
      { rwa [← card_pos, card_erase_of_mem Hx, nat.lt_pred_iff] },
      { rwa [← card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, nat.lt_pred_iff] },
      { apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_of_subset_right (erase_subset _ _), assumption },
      { rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size] },
      { apply lt_of_le_of_lt (max'_le (erase U x) _ _ (λ y, le_max' U Uh y ∘ mem_of_mem_erase)), 
        apply lt_of_lt_of_le max_lt (le_max' _ _ _ _),
        rw mem_erase, refine ⟨(min_ne_max_of_card _).symm, max'_mem _ _⟩, 
        rwa ← same_size } },
    rw ← card_pos at Uh,
    replace p: card U = 1 := le_antisymm p Uh,
    rw p at same_size,
    have: erase U x = ∅,
      rw [← card_eq_zero, card_erase_of_mem Hx, p], refl,
    have: erase V (min' V Vh) = ∅,
      rw [← card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size], refl,
    rw [‹erase U x = ∅›, ‹erase V (min' V Vh) = ∅›],
    apply is_compressed_empty
  end

  instance thing2 [decidable_linear_order α] (U V : finset α) : decidable (useful_compression U V) := by rw useful_compression; apply_instance

  -- The main KK helper: use induction with our measure and compression_improved to keep compressing until 
  -- we can't any more, which gives a set family which is fully compressed.
  lemma kruskal_katona_helper (r : ℕ) (𝒜 : finset (finset (fin n))) (h : all_sized 𝒜 r) : 
    ∃ (ℬ : finset (finset (fin n))), (∂ℬ).card ≤ (∂𝒜).card ∧ 𝒜.card = ℬ.card ∧ all_sized ℬ r ∧ (∀ U V, useful_compression U V → is_compressed U V ℬ) := 
  begin
    refine @well_founded.recursion _ _ (measure_wf family_measure_fin) (λ (A : finset (finset (fin n))), all_sized A r → ∃ B, (∂B).card ≤ (∂A).card ∧ A.card = B.card ∧ all_sized B r ∧ ∀ (U V : finset (fin n)), useful_compression U V → is_compressed U V B) _ _ h,
    intros A ih z,
    -- Are there any compressions we can make now?
    set usable: finset (finset (fin n) × finset (fin n)) := filter (λ t, useful_compression t.1 t.2 ∧ ¬ is_compressed t.1 t.2 A) ((powerset univ).product (powerset univ)), 
    -- No. Then where we are is the required set family.
    by_cases (usable = ∅),
      refine ⟨A, le_refl _, rfl, z, _⟩, intros U V k,
      rw eq_empty_iff_forall_not_mem at h,
      by_contra,
      apply h ⟨U,V⟩,
      simp [a, k], exact ⟨subset_univ _, subset_univ _⟩,
    -- Yes. Then apply the compression, then keep going
    rcases exists_min usable (λ t, t.1.card) ((nonempty_iff_ne_empty _).2 h) with ⟨⟨U,V⟩, uvh, t⟩, rw mem_filter at uvh,
    have h₂: ∀ U₁ V₁, useful_compression U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ A,
      intros U₁ V₁ h, by_contra, 
      apply not_le_of_gt h.2 (t ⟨U₁, V₁⟩ _),
      simp [h, a], exact ⟨subset_univ _, subset_univ _⟩,
    obtain ⟨small_measure, p2, layered, p1⟩ := compression_improved U V A z uvh.2.1 h₂ uvh.2.2, 
    rw [measure, inv_image] at ih, 
    rcases ih (compress_family U V A) small_measure layered with ⟨B, q1, q2, q3, q4⟩,
    exact ⟨B, trans q1 p1, trans p2.symm q2, q3, q4⟩
  end

  -- is_init_seg_of_colex 𝒜 r means that everything in 𝒜 has size r, and that if B is below A in colex where B has size r and A is in 𝒜,
  -- then B is also in 𝒜
  def is_init_seg_of_colex [has_lt α] (𝒜 : finset (finset α)) (r : ℕ) : Prop := all_sized 𝒜 r ∧ (∀ A ∈ 𝒜, ∀ B, B <ᶜ A ∧ B.card = r → B ∈ 𝒜)

  -- Initial segments are nested in some way
  lemma init_seg_total [decidable_linear_order α] (𝒜₁ 𝒜₂ : finset (finset α)) (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜₁ r) (h₂ : is_init_seg_of_colex 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ :=
  begin
    rw ← sdiff_eq_empty_iff_subset, rw ← sdiff_eq_empty_iff_subset,
    by_contra a, rw not_or_distrib at a, simp [exists_mem_iff_ne_empty.symm, exists_mem_iff_ne_empty.symm] at a,
    rcases a with ⟨⟨A, Ah₁, Ah₂⟩, ⟨B, Bh₁, Bh₂⟩⟩,
    rcases trichotomous_of (<ᶜ) A B with lt | eq | gt,
      { exact Ah₂ (h₂.2 B Bh₁ A ⟨lt, h₁.1 A Ah₁⟩) },
      { rw eq at Ah₁, exact Bh₂ Ah₁ },
      { exact Bh₂ (h₁.2 A Ah₁ B ⟨gt, h₂.1 B Bh₁⟩) },
  end

  -- If we're compressed by all useful compressions, we're an initial segment
  lemma init_seg_of_compressed [decidable_linear_order α] (ℬ : finset (finset α)) (r : ℕ) (h₁ : all_sized ℬ r) (h₂ : ∀ U V, useful_compression U V → is_compressed U V ℬ): 
    is_init_seg_of_colex ℬ r := 
  begin
    refine ⟨h₁, _⟩,
    rintros B Bh A ⟨A_lt_B, sizeA⟩,
    by_contra a,
    set U := A \ B,
    set V := B \ A,
    have: A ≠ B, intro t, rw t at a, exact a Bh,
    have: disjoint U B ∧ V ⊆ B := ⟨sdiff_disjoint, sdiff_subset_left _ _⟩,
    have: disjoint V A ∧ U ⊆ A := ⟨sdiff_disjoint, sdiff_subset_left _ _⟩,
    have cB_eq_A: compress U V B = A,
    { rw compress, split_ifs, rw [union_sdiff_self_eq_union, union_sdiff_distrib_right, sdiff_eq_self_of_disjoint disjoint_sdiff, union_comm], 
      apply union_eq_left_of_subset,
      intro t, simp only [and_imp, not_and, mem_sdiff, not_not], exact (λ x y, y x) },
    have cA_eq_B: compress V U A = B,
    { rw compress, split_ifs, rw [union_sdiff_self_eq_union, union_sdiff_distrib_right, sdiff_eq_self_of_disjoint disjoint_sdiff, union_comm], 
      apply union_eq_left_of_subset,
      intro t, simp only [and_imp, not_and, mem_sdiff, not_not], exact (λ x y, y x) },
    have: card A = card B := trans sizeA (h₁ B Bh).symm,
    have hU: U ≠ ∅,
      { intro t, rw sdiff_eq_empty_iff_subset at t, have: A = B := eq_of_subset_of_card_le t (ge_of_eq ‹_›), rw this at a, exact a Bh },
    have hV: V ≠ ∅,
      { intro t, rw sdiff_eq_empty_iff_subset at t, have: B = A := eq_of_subset_of_card_le t (le_of_eq ‹_›), rw ← this at a, exact a Bh },
    have disj: disjoint U V,
      { exact disjoint_of_subset_left (sdiff_subset_left _ _) disjoint_sdiff },
    have smaller: max' U hU < max' V hV,
      { rcases lt_trichotomy (max' U hU) (max' V hV) with lt | eq | gt,
        { assumption },
        { exfalso, have: max' U hU ∈ U := max'_mem _ _, apply disjoint_left.1 disj this, rw eq, exact max'_mem _ _ },
        { exfalso, have z := compression_reduces_set A gt, rw cA_eq_B at z,
          apply asymm A_lt_B (z ‹A ≠ B›.symm) } },
    have: useful_compression U V,
    { refine ⟨hU, hV, disj, _, smaller⟩,
      have: card (A \ B ∪ A ∩ B) = card (B \ A ∪ B ∩ A),
        rwa [sdiff_union_inter, sdiff_union_inter],
      rwa [card_disjoint_union (sdiff_inter_inter _ _), card_disjoint_union (sdiff_inter_inter _ _), inter_comm, add_right_inj] at this
    },
    have Bcomp := h₂ U V this, rw is_compressed at Bcomp,
    suffices: compress U V B ∈ compress_family U V ℬ,
      rw [Bcomp, cB_eq_A] at this, exact a this,
    rw mem_compress, left, refine ⟨_, B, Bh, rfl⟩, rwa cB_eq_A, 
  end

  -- These currently aren't used but I think they could be
  -- They give initial segments of colex with α = ℕ, in a different way to everything_up_to below.
  -- KK could also in theory work with these

  -- def all_under (A : finset ℕ) : finset (finset ℕ) := A.bind (λ k, filter (λ B, card A = card B) (image (λ B, B ∪ A.filter (λ x, x > k)) (powerset (range k))))
  -- def all_up_to (A : finset ℕ) : finset (finset ℕ) := all_under A ∪ finset.singleton A

  -- lemma mem_all_under (A B : finset ℕ) : B ∈ all_under A ↔ card A = card B ∧ B <ᶜ A :=
  -- begin
  --   simp [all_under, colex_lt], split,
  --     rintro ⟨k, kinA, ⟨lows, lows_small, rfl⟩, cards⟩,
  --     refine ⟨cards, k, _, _, kinA⟩, intros x hx, simp [hx], 
  --       convert false_or _, simp only [eq_iff_iff, iff_false], intro, apply not_lt_of_gt hx, rw ← mem_range, apply lows_small a,
  --     simp [kinA, not_or_distrib, le_refl], 
  --     intro, have := lows_small a, apply not_mem_range_self this, 
  --   rintro ⟨cards, k, z, knotinB, kinA⟩, 
  --   refine ⟨k, kinA, ⟨filter (λ x, x < k) B, _, _⟩, cards⟩, 
  --   intro, simp,
  --   ext, simp, split, 
  --     rintro (⟨a1l, a1r⟩ | ⟨a2l, a2r⟩), rwa z a1r, 
  --     exact a2l,
  --   intro, rcases (lt_or_gt_of_ne (ne_of_mem_of_not_mem a_1 knotinB)), 
  --     right, exact ⟨‹_›, h⟩, 
  --   left, rw ← z h, exact ⟨a_1, h⟩
  -- end

  -- lemma mem_all_up_to (A B : finset ℕ) : B ∈ all_up_to A ↔ (card A = card B ∧ B <ᶜ A) ∨ B = A :=
  -- by simp [all_up_to, mem_all_under]; tauto

  -- Gives all sets up to A with the same size as it: this is equivalent to being an initial segment of colex...
  def everything_up_to [fintype α] [decidable_linear_order α] (A : finset α) : finset (finset α) := filter (λ (B : finset α), A.card = B.card ∧ B ≤ᶜ A) (powerset univ)

  lemma mem_everything_up_to [fintype α] [decidable_linear_order α] (A B : finset α) : B ∈ everything_up_to A ↔ A.card = B.card ∧ B ≤ᶜ A :=
  begin
    rw everything_up_to, rw mem_filter, rw mem_powerset, split, tauto, 
    intro a, refine ⟨subset_univ _, a⟩,
  end

  -- ...which is proved here.
  lemma IS_iff_le_max [fintype α] [decidable_linear_order α] (𝒜 : finset (finset α)) (r : ℕ) : 
    𝒜 ≠ ∅ ∧ is_init_seg_of_colex 𝒜 r ↔ ∃ (A : finset α), A ∈ 𝒜 ∧ A.card = r ∧ 𝒜 = everything_up_to A := 
  begin
    rw is_init_seg_of_colex, split, 
    { rintro ⟨ne, layer, IS⟩,
      have Ah := @max'_mem _ colex_decidable_order 𝒜 ne,
      refine ⟨max' 𝒜 ne, Ah, layer _ Ah, _⟩, ext B, rw mem_everything_up_to, split,
        intro p, rw [layer _ p, layer _ Ah], refine ⟨rfl, le_max' _ ne _ p⟩, 
      rintro ⟨cards, le⟩, rcases le with p | rfl, 
      apply IS _ Ah _ ⟨p, cards ▸ layer _ Ah⟩, exact Ah },
    { rintro ⟨A, Ah, Ac, rfl⟩, 
      refine ⟨ne_empty_of_mem Ah, λ B Bh, _, _⟩, rw mem_everything_up_to at Bh, rwa ← Bh.1,  
      intros B₁ Bh₁ B₂ Bh₂, rw mem_everything_up_to, split, rwa Bh₂.2, 
      rw mem_everything_up_to at Bh₁, exact trans (or.inl Bh₂.1) Bh₁.2 }
  end

  lemma up_to_is_IS [decidable_linear_order α] [fintype α] {A : finset α} {r : ℕ} (h₁ : A.card = r) : is_init_seg_of_colex (everything_up_to A) r := 
  and.right $ (IS_iff_le_max _ _).2 
  (by refine ⟨A, _, h₁, rfl⟩; simp [mem_everything_up_to, refl_of (≤ᶜ) A])

  -- This is important for iterated KK: the shadow of an everything_up_to is also an everything_up_to...
  lemma shadow_of_everything_up_to [decidable_linear_order α] [fintype α] (A : finset α) (hA : A ≠ ∅) : ∂ (everything_up_to A) = everything_up_to (erase A (min' A hA)) :=
  begin
    -- This is a pretty painful proof, with lots of cases.
    ext B, simp [mem_shadow', mem_everything_up_to], split,
      -- First show that if B ∪ i ≤ A, then B ≤ A - min A
      rintro ⟨i, ih, p, t⟩,
      rw [card_insert_of_not_mem ih] at p,
      have cards: card (erase A (min' A hA)) = card B,
        rw [card_erase_of_mem (min'_mem _ _), p], refl,
      rcases t with ⟨k, z, _, _⟩ | h, -- cases on B ∪ i = A or B ∪ i < A
      { simp [cards], have: k ≠ i, rintro rfl, exact ‹k ∉ insert k B› (mem_insert_self _ _), 
        -- B ∪ i < A, with k as the colex witness. Cases on k < i or k > i.
        cases lt_or_gt_of_ne this, 
        { left, refine ⟨i, λ x hx, _, ih, _⟩, -- When k < i, then i works as the colex witness to show B < A - min A
          { split; intro p, apply mem_erase_of_ne_of_mem, apply ne_of_gt (trans hx (lt_of_le_of_lt (min'_le _ _ _ ‹_›) h)), 
              rw ← z (trans h hx), apply mem_insert_of_mem p, 
            apply mem_of_mem_insert_of_ne _ (ne_of_gt hx), rw z (trans h hx), apply mem_of_mem_erase p },
          apply mem_erase_of_ne_of_mem, apply ne_of_gt (lt_of_le_of_lt _ h), apply min'_le, assumption,
          rw ← z h, apply mem_insert_self }, 
        { rcases lt_or_eq_of_le (min'_le _ hA _ ‹k ∈ A›) with h₁ | rfl, -- When k > i, cases on min A < k or min A = k
            -- If min A < k, k works as the colex witness for B < A - min A
            left, refine ⟨k, λ x hx, _, ‹k ∉ insert i B› ∘ mem_insert_of_mem, mem_erase_of_ne_of_mem (ne_of_gt h₁) ‹_›⟩, 
            simp [ne_of_gt (trans hx h₁)], rw ← z hx, rw mem_insert, simp [ne_of_gt (trans hx h)], 
          -- If k = min A, then B = A - min A
          right, symmetry, apply eq_of_subset_of_card_le _ (ge_of_eq cards), intros t ht, 
          rw [mem_erase] at ht, have: t ≠ i := ne_of_gt (lt_of_lt_of_le h (min'_le _ _ _ ht.2)), 
          rw ← z _ at ht, apply mem_of_mem_insert_of_ne ht.2 ‹t ≠ i›, apply lt_of_le_of_ne (min'_le _ _ _ ht.2), 
          symmetry, exact ht.1 } },
      { refine ⟨cards, _⟩, -- Here B ∪ i = A, do cases on i = min A or not
        by_cases q: (i = min' A hA),
          right, rw ← q, rw ← h, rw erase_insert ih, 
        left, refine ⟨i, λ x hx, _, ih, mem_erase_of_ne_of_mem q (h ▸ mem_insert_self _ _)⟩, rw mem_erase, split,
        intro, split, apply ne_of_gt, apply lt_of_le_of_lt _ hx, apply min'_le, rw ← h, apply mem_insert_self,
        rw ← h, apply mem_insert_of_mem a, rintro ⟨a, b⟩, rw ← h at b, apply mem_of_mem_insert_of_ne b (ne_of_gt hx) },
    -- Now show that if B ≤ A - min A, there is j such that B ∪ j ≤ A
    -- We choose j as the smallest thing not in B
    rintro ⟨cards', ⟨k, z, _, _⟩ | rfl⟩, set j := min' (univ \ B) (ne_empty_of_mem (mem_sdiff.2 ⟨complete _, ‹_›⟩)), 
      -- Assume first B < A - min A, and take k as the colex witness for this
      have r: j ≤ k := min'_le _ _ _ _, 
      have: j ∉ B, have: j ∈ univ \ B := min'_mem _ _, rw mem_sdiff at this, exact this.2,
      have cards: card A = card (insert j B),
      { rw [card_insert_of_not_mem ‹j ∉ B›, ← ‹_ = card B›, card_erase_of_mem (min'_mem _ _), nat.pred_eq_sub_one, nat.sub_add_cancel], 
      apply nat.pos_of_ne_zero, rw ne, rw card_eq_zero, exact hA },
      refine ⟨j, ‹_›, cards, _⟩, 
      rcases lt_or_eq_of_le r with r | r₁, -- cases on j < k or j = k
        -- if j < k, k is our colex witness for B ∪ j < A
        left, refine ⟨k, _, mt (λ t, mem_of_mem_insert_of_ne t (ne_of_gt r)) ‹k ∉ B›, mem_of_mem_erase ‹_›⟩, intros x hx, 
        rw mem_insert, rw z hx, simp [ne_of_gt (trans hx r), ne_of_gt (lt_of_le_of_lt (min'_le _ _ _ (mem_of_mem_erase ‹_›)) hx)], 
      -- if j = k, all of range k is in B so by sizes B ∪ j = A
      right, symmetry, apply eq_of_subset_of_card_le, intros t th, rcases lt_trichotomy k t with lt|eq|gt,
      { apply mem_insert_of_mem, rw z lt, apply mem_erase_of_ne_of_mem _ th, apply ne_of_gt (lt_of_le_of_lt _ lt), apply min'_le _ _ _ (mem_of_mem_erase ‹_›) },
      { rw [← eq, r₁], apply mem_insert_self },
      { apply mem_insert_of_mem, rw ← r₁ at gt, by_contra, apply not_lt_of_le (min'_le (univ \ B) _ t _) gt, rw mem_sdiff, exact ⟨complete _, a⟩ },
      apply ge_of_eq cards, rw mem_sdiff, exact ⟨complete _, ‹_›⟩, 
    -- If B = A - min A, then use j = min A so B ∪ j = A
    refine ⟨min' A hA, not_mem_erase _ _, _⟩, 
    rw insert_erase (min'_mem _ _), exact ⟨rfl, refl _⟩
  end

  -- ...which we use to prove that the shadow of an initial segment is also an initial segment.
  lemma shadow_of_IS [decidable_linear_order α] [fintype α] {𝒜 : finset (finset α)} (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜 r) : is_init_seg_of_colex (∂𝒜) (r - 1) :=
  begin
    rcases nat.eq_zero_or_pos r with rfl | hr,
      have: 𝒜 ⊆ finset.singleton ∅,
        intros A hA, rw mem_singleton, rw ← card_eq_zero, apply h₁.1 A hA,  
      have := shadow_monotone this,
      simp only [all_removals, shadow, subset_empty, singleton_bind, image_empty] at this,
      simp [shadow, this, is_init_seg_of_colex, all_sized],
    by_cases h₂: 𝒜 = ∅,
      rw h₂, rw shadow_empty, rw is_init_seg_of_colex, rw all_sized, simp,
    replace h₁ := and.intro h₂ h₁,
    rw IS_iff_le_max at h₁,
    rcases h₁ with ⟨B, _, rfl, rfl⟩, 
    rw shadow_of_everything_up_to, 
      apply up_to_is_IS,
      rw card_erase_of_mem (min'_mem _ _), refl,
    rwa ← card_pos
  end
end
end UV

local notation `X` := fin n
-- Finally we can prove KK.
section KK
  -- Most of the work was done in KK helper; it gives a ℬ which is fully compressed, and so we know it's an initial segment.
  theorem kruskal_katona (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    all_sized 𝒜 r ∧ all_sized 𝒞 r ∧ 𝒜.card = 𝒞.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (∂𝒞).card ≤ (∂𝒜).card :=
  begin
    rintros ⟨layerA, layerC, h₃, h₄⟩,
    rcases UV.kruskal_katona_helper r 𝒜 layerA with ⟨ℬ, _, t, layerB, fully_comp⟩,
    have: UV.is_init_seg_of_colex ℬ r := UV.init_seg_of_compressed ℬ r layerB fully_comp,
    suffices: 𝒞 = ℬ,
      rwa this at *,
    have z: card ℬ = card 𝒞 := t.symm.trans h₃,
    cases UV.init_seg_total ℬ 𝒞 r this h₄ with BC CB,
      symmetry, apply eq_of_subset_of_card_le BC (ge_of_eq z),
    apply eq_of_subset_of_card_le CB (le_of_eq z)
  end

  -- We can strengthen KK slightly: note the middle and has been relaxed to a ≤.
  -- This shows that the minimum possible shadow size is attained by initial segments.
  theorem strengthened (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    all_sized 𝒜 r ∧ all_sized 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (∂𝒞).card ≤ (∂𝒜).card :=
  begin
    rintros ⟨Ar, Cr, cards, colex⟩,
    rcases exists_smaller_set 𝒜 𝒞.card cards with ⟨𝒜', prop, size⟩,
    have := kruskal_katona r 𝒜' 𝒞 ⟨λ A hA, Ar _ (prop hA), Cr, size, colex⟩,
    transitivity, exact this, apply card_le_of_subset, rw [shadow, shadow], apply shadow_monotone prop
  end

  -- We can also iterate the strengthened form, since the shadow of an inital segment is initial.
  -- In particular, the minimum possible iterated shadow size is attained by initial segments.
  theorem iterated (r k : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    all_sized 𝒜 r ∧ all_sized 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (shadow^[k] 𝒞).card ≤ (shadow^[k] 𝒜).card :=
  begin
    revert r 𝒜 𝒞, induction k,
      intros, simp, exact a.2.2.1,
    rintros r A C ⟨z₁, z₂, z₃, z₄⟩, simp, apply k_ih (r-1), refine ⟨shadow_layer z₁, shadow_layer z₂, _, _⟩,
    apply strengthened r _ _ ⟨z₁, z₂, z₃, z₄⟩, 
    apply UV.shadow_of_IS _ z₄
  end

  -- A special case of KK which is sometimes easier to work with. 
  -- If |𝒜| ≥ k choose r, (and everything in 𝒜 has size r) then the initial segment we compare to
  -- is just all the subsets of {0,...,k-1} of size r. The ith iterated shadow of this is
  -- all the subsets of {0,...,k-1} of size r-i, so the ith iterated shadow of 𝒜 has at least k choose (r-i) 
  -- elements
  theorem lovasz_form {r k i : ℕ} {𝒜 : finset (finset X)} (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n) (h₁ : all_sized 𝒜 r) (h₂ : nat.choose k r ≤ 𝒜.card) : 
    nat.choose k (r-i) ≤ (shadow^[i] 𝒜).card :=
  begin
    set range'k : finset X := attach_fin (range k) (λ m, by rw mem_range; apply forall_lt_iff_le.2 hkn),
    set 𝒞 : finset (finset X) := powerset_len r (range'k),
    have Ccard: 𝒞.card = nat.choose k r,
      rw [card_powerset_len, card_attach_fin, card_range], 
    have: all_sized 𝒞 r, intros A HA, rw mem_powerset_len at HA, exact HA.2,
    suffices this: (shadow^[i] 𝒞).card = nat.choose k (r-i),
    { rw ← this, apply iterated r _ _ _ ⟨h₁, ‹all_sized 𝒞 r›, _, _⟩, 
      rwa Ccard, 
      refine ⟨‹_›, _⟩, rintros A HA B ⟨HB₁, HB₂⟩, 
      rw mem_powerset_len, refine ⟨_, ‹_›⟩, 
      intros t th, rw mem_attach_fin, rw mem_range, 
      have: image fin.val B <ᶜ image fin.val A, rwa colex_hom_fin,
      apply max_colex k this _ t.val _, intros x hx, rw mem_image at hx, rw mem_powerset_len at HA, rcases hx with ⟨a, ha, q⟩, rw ← q, rw ← mem_range, have := HA.1 ha, rwa mem_attach_fin at this, 
      rw mem_image, refine ⟨t, th, rfl⟩ },
    suffices: (shadow^[i] 𝒞) = powerset_len (r-i) range'k,
      rw [this, card_powerset_len, card_attach_fin, card_range], 
    ext B, rw mem_powerset_len, rw sub_iff_shadow_iter, 
    split, 
      rintro ⟨A, Ah, BsubA, card_sdiff_i⟩,
      rw mem_powerset_len at Ah, refine ⟨subset.trans BsubA Ah.1, _⟩, symmetry,
      rw nat.sub_eq_iff_eq_add, 
      rw ← Ah.2, rw ← card_sdiff_i, rw ← card_disjoint_union, rw union_sdiff_of_subset BsubA,  apply disjoint_sdiff,
      apply hir,
    rintro ⟨_, _⟩,
    rcases exists_intermediate_set _ _ i _ a_left with ⟨C, BsubC, Csubrange, cards⟩, 
    rw [a_right, ← nat.add_sub_assoc hir, nat.add_sub_cancel_left] at cards, 
    refine ⟨C, _, BsubC, _⟩,
    rw mem_powerset_len, exact ⟨Csubrange, cards⟩, 
    rw card_sdiff BsubC, rw cards, rw a_right, rw nat.sub_sub_self hir, 
    rw a_right, rw card_attach_fin, rw card_range, rw ← nat.add_sub_assoc hir, rwa nat.add_sub_cancel_left, 
  end
end KK

-- An application of KK: intersecting families. A set family is intersecting if every pair of sets has something in common.
def intersecting (𝒜 : finset (finset X)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ¬ disjoint A B

-- The maximum size of an intersecting family is 2^(n-1). This is attained by taking, for instance, everything with a 0 in it.
theorem intersecting_all {𝒜 : finset (finset X)} (h : intersecting 𝒜) : 𝒜.card ≤ 2^(n-1) :=
begin
  cases nat.eq_zero_or_pos n with b hn,
    convert nat.zero_le _,
    rw [card_eq_zero, eq_empty_iff_forall_not_mem],
    intros A HA, apply h A HA A HA, rw disjoint_self_iff_empty, 
    rw eq_empty_iff_forall_not_mem, intro x, rw b at x, exact (fin.elim0 ‹_›),
  set f : finset X → finset (finset X) := λ A, insert (univ \ A) (finset.singleton A),
  have disjs: ∀ x ∈ 𝒜, ∀ y ∈ 𝒜, x ≠ y → disjoint (f x) (f y),
    intros A hA B hB k,
    simp [not_or_distrib, and_assoc], refine ⟨_, _, _, _⟩,
      { intro z, apply k, ext a, simp [ext] at z, replace z := z a, tauto },
      intro a, rw ← a at hA, apply h _ hB _ hA disjoint_sdiff, 
      intro a, rw ← a at hB, apply h _ hB _ hA sdiff_disjoint, 
      exact k.symm, 
  have: 𝒜.bind f ⊆ powerset univ,
    intros A hA, rw mem_powerset, apply subset_univ,
  have q := card_le_of_subset this, rw [card_powerset, card_univ, card_fin] at q, 
  rw card_bind disjs at q, dsimp at q,
  have: ∀ u ∈ 𝒜, card (f u) = 2,
    intros u _, rw card_insert_of_not_mem, rw card_singleton, rw mem_singleton, intro, simp [ext] at a, apply a, exact ⟨0, hn⟩,
  rw sum_const_nat this at q,
  rw ← nat.le_div_iff_mul_le' zero_lt_two at q, 
  conv_rhs at q {rw ← nat.sub_add_cancel hn},
  rw nat.pow_add at q, simp at q, assumption,
end

def extremal_intersecting (hn : 1 ≤ n) : finset (finset X) :=
(powerset univ).filter (λ A, (⟨0, hn⟩: X) ∈ A)

-- This suggests the question: What's the maximum size of an intersecting family, if all sets have size r?
-- For r > n/2, we can just take all sets of size r - by pigeonhole this is intersecting, so the maximum is n choose r.
-- For r ≤ n/2, we can get a tighter bound: (n-1) choose (r-1), using the Lovasz form of KK.
-- (Other proofs are possible.)
theorem EKR {𝒜 : finset (finset X)} {r : ℕ} (h₁ : intersecting 𝒜) (h₂ : all_sized 𝒜 r) (h₃ : r ≤ n/2) : 𝒜.card ≤ nat.choose (n-1) (r-1) :=
begin
  -- Take care of the r=0 case first: it's not very interesting.
  cases nat.eq_zero_or_pos r with b h1r,
    convert nat.zero_le _,
    rw [card_eq_zero, eq_empty_iff_forall_not_mem],
    intros A HA, apply h₁ A HA A HA, rw disjoint_self_iff_empty, 
    rw ← card_eq_zero, rw ← b, apply h₂ _ HA,
  apply le_of_not_lt, intro size,
  -- Consider 𝒜bar = {A^c | A ∈ 𝒜}
  set 𝒜bar := 𝒜.image (λ A, univ \ A),
  -- Then its iterated shadow (∂^[n-2k] 𝒜bar) is disjoint from 𝒜 by intersecting-ness
  have: disjoint 𝒜 (shadow^[n-2*r] 𝒜bar),
    rw disjoint_right, intros A hAbar hA, 
    simp [sub_iff_shadow_iter, mem_image] at hAbar,
    rcases hAbar with ⟨_, ⟨C, hC, rfl⟩, AsubnotC, _⟩, 
    apply h₁ A hA C hC (disjoint_of_subset_left AsubnotC sdiff_disjoint),
  have: r ≤ n := trans h₃ (nat.div_le_self n 2), 
  have: 1 ≤ n := trans ‹1 ≤ r› ‹r ≤ n›,
  -- We know the size of 𝒜bar since it's the same size as 𝒜
  have z: 𝒜bar.card > nat.choose (n-1) (n-r),
    convert size using 1, rw card_image_of_inj_on, intros A _ B _ k, replace k := sdiff_partially_injective k,
      simp [ext] at k, rwa ext,
    apply choose_symm', rw [← nat.add_sub_assoc ‹r ≥ 1›, nat.sub_add_cancel ‹r ≤ n›],
  -- and everything in 𝒜bar has size n-r.
  have: all_sized 𝒜bar (n - r),
    intro A, rw mem_image, rintro ⟨B, Bz, rfl⟩, rw card_univ_diff, rw card_fin, rw h₂ _ Bz, 
  have: n - 2 * r ≤ n - r, rw nat.sub_le_sub_left_iff ‹r ≤ n›, apply nat.le_mul_of_pos_left zero_lt_two,
  -- So, we can use the Lovasz form of KK to get |∂^[n-2k] 𝒜bar| ≥ (n-1) choose r
  have kk := lovasz_form ‹n - 2 * r ≤ n - r› (by rwa nat.sub_le_sub_left_iff (trans h1r ‹r ≤ n›)) (nat.sub_le_self _ _) ‹all_sized 𝒜bar (n - r)› (le_of_lt z), 
  have q: n - r - (n - 2 * r) = r, rw [nat.sub.right_comm, nat.sub_sub_self, two_mul], apply nat.add_sub_cancel,
    rw [mul_comm, ← nat.le_div_iff_mul_le' zero_lt_two], apply h₃, 
  rw q at kk, 
  -- But this gives a contradiction: |𝒜| + |∂^[n-2k] 𝒜bar| > n choose r
  have: nat.choose n r < card (𝒜 ∪ (shadow^[n - 2 * r] 𝒜bar)),
    rw card_disjoint_union ‹_›, 
    convert lt_of_le_of_lt (nat.add_le_add_left kk _) (nat.add_lt_add_right size _),
    convert nat.choose_succ_succ _ _, any_goals {rwa [nat.sub_one, nat.succ_pred_eq_of_pos]}, 
  apply not_le_of_lt this,
  convert number_of_fixed_size _, rw card_fin,
  rw ← union_layer, refine ⟨‹_›, _⟩,
  convert iter_shadow_sized ‹all_sized 𝒜bar (n - r)›, 
  rw q
end