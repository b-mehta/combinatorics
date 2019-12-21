import algebra.geom_sum
import data.finset
import data.fintype
import tactic
import to_mathlib
import basic
import shadows

open fintype
open finset
open nat

variable {α : Type*}
variables [decidable_eq α] -- [decidable_linear_order α]

variables {n : ℕ}
local notation `X` := fin n


lemma sperner [fintype α] {𝒜 : finset (finset α)} (H : antichain 𝒜) : 𝒜.card ≤ nat.choose (card α) (card α / 2) := 
begin
  have q1 := lubell_yamamoto_meshalkin H,
  set f := (λ (r : ℕ), ((𝒜#r).card : ℚ) / nat.choose (card α) r),
  set g := (λ (r : ℕ), ((𝒜#r).card : ℚ) / nat.choose (card α) (card α/2)),
  have q2 : sum (range (card α + 1)) g ≤ sum (range (card α + 1)) f,
    apply sum_le_sum,
    intros r hr,
    apply div_le_div_of_le_left; norm_cast,
        apply nat.zero_le,
      apply nat.choose_pos,
      rw mem_range at hr,
      rwa ← nat.lt_succ_iff,
    apply dominate_choose,
  
  have := trans q2 q1,
  rw [← sum_div, ← sum_nat_cast, div_le_one_iff_le] at this,
    swap, norm_cast, apply nat.choose_pos (nat.div_le_self _ _),
  norm_cast at this,
  rw ← card_bind at this,
    suffices m: finset.bind (range (card α + 1)) (λ (u : ℕ), 𝒜#u) = 𝒜,
      rwa m at this,
    ext,
    rw mem_bind,
    split, rintro ⟨_,_,q⟩,
      rw mem_slice at q,
      exact q.1,
    intro, 
    refine ⟨a.card, _, _⟩,
      rw [mem_range, nat.lt_succ_iff],
      apply card_le_of_subset (subset_univ a),
    rw mem_slice,
    tauto,
  intros x _ y _ ne,
  rw disjoint_left,
  intros a Ha k,
  exact ne_of_diff_slice Ha k ne rfl
end

namespace ij
section 
  variables (i j : X)
  
  def compress (i j : α) (A : finset α) : finset α := 
  if (j ∈ A ∧ i ∉ A)
    then insert i (A.erase j)
    else A

  lemma compressed_set (i j : α) {A : finset α} : ¬ (j ∈ compress i j A ∧ i ∉ compress i j A) :=
  begin
    intro,
    rw compress at a,
    split_ifs at a,
      apply a.2,
      apply mem_insert_self,
    exact h a
  end

  lemma compress_idem (i j : α) (A : finset α) : compress i j (compress i j A) = compress i j A :=
  begin
    rw compress,
    split_ifs,
      exfalso,
      apply compressed_set _ _ h,
    refl
  end

  @[reducible] def compress_remains (i j : α) (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.filter (λ A, compress i j A ∈ 𝒜)
  @[reducible] def compress_motion (i j : α) (𝒜 : finset (finset α)) : finset (finset α) := (𝒜.filter (λ A, compress i j A ∉ 𝒜)).image (compress i j)

  def compress_family (i j : α) (𝒜 : finset (finset α)) : finset (finset α) :=
  compress_motion i j 𝒜 ∪ compress_remains i j 𝒜

  lemma mem_compress_remains (𝒜 : finset (finset α)) (i j : α) (A : finset α) : A ∈ compress_remains i j 𝒜 ↔ A ∈ 𝒜 ∧ compress i j A ∈ 𝒜 :=
  by rw mem_filter

  lemma mem_compress_motion (𝒜 : finset (finset α)) (i j : α) (A : finset α) : A ∈ compress_motion i j 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress i j B = A) :=
  begin
    simp [compress_motion], 
    split; rintro ⟨p, q, r⟩,
      exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
    exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩, 
  end

  lemma mem_compress (𝒜 : finset (finset α)) (i j : α) (A : finset α) : 
    A ∈ compress_family i j 𝒜 ↔ (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress i j B = A)) ∨ (A ∈ 𝒜 ∧ compress i j A ∈ 𝒜) :=
  by rw [compress_family, mem_union, mem_compress_remains, mem_compress_motion]

  lemma compress_disjoint (𝒜 : finset (finset α)) (i j : α) : disjoint (compress_motion i j 𝒜) (compress_remains i j 𝒜) :=
  begin
    rw disjoint_left,
    intros A HA HB,
    rw mem_compress_remains at HB,
    rw mem_compress_motion at HA,
    exact HA.1 HB.1
  end

  lemma inj_ish {i j : α} {A B : finset α} (hA : j ∈ A ∧ i ∉ A) (hY : j ∈ B ∧ i ∉ B) 
    (Z : insert i (erase A j) = insert i (erase B j)) : A = B := 
  begin
    ext x, split,
    all_goals { intro p, 
                by_cases h₁: (x=j), {rw h₁, tauto}, 
                have h₂: x ≠ i, {intro, rw a at p, tauto},
                rw ext at Z,
                replace Z := Z x,
                simp only [mem_insert, mem_erase] at Z,
                tauto }
  end

  lemma compressed_size (𝒜 : finset (finset α)) (i j : α) : (compress_family i j 𝒜).card = 𝒜.card :=
  begin
    rw [compress_family, card_disjoint_union (compress_disjoint _ _ _), card_image_of_inj_on],
      rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
      rw [disjoint_iff_inter_eq_empty, inter_comm],
      apply filter_inter_filter_neg_eq,
    intros A HX Y HY Z,
    rw mem_filter at HX HY,
    rw compress at HX Z,
    split_ifs at HX Z,
      rw compress at HY Z,
      split_ifs at HY Z,
        exact inj_ish h h_1 Z,
      tauto,
    tauto
  end

  lemma insert_erase_comm {i j : α} {A : finset α} (h : i ≠ j) : insert i (erase A j) = erase (insert i A) j :=
  begin
    simp only [ext, mem_insert, mem_erase],
    intro x,
    split; intro p,
      cases p, split, rw p, 
    all_goals {tauto},
  end

  lemma compress_moved {𝒜 : finset (finset α)} {i j : α} {A : finset α} (h₁ : A ∈ compress_family i j 𝒜) (h₂ : A ∉ 𝒜) : 
    i ∈ A ∧ j ∉ A ∧ erase (insert j A) i ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
      rw compress at HB,
      split_ifs at HB,
        rw ← HB,
        refine ⟨mem_insert_self _ _, _, _⟩,
          rw mem_insert,
          intro,
          rcases a with rfl, tauto,
          exact not_mem_erase j B a,
        have: erase (insert j (insert i (erase B j))) i = B,
          rw [insert_erase_comm, insert_erase (mem_insert_of_mem h.1), erase_insert h.2], 
          rintro rfl, tauto,
        rwa this,
      rw HB at H, tauto,
    tauto
  end

  lemma compress_held {𝒜 : finset (finset α)} {i j : α} {A : finset α} (h₁ : j ∈ A) (h₂ : A ∈ compress_family i j 𝒜) : A ∈ 𝒜 :=
  begin
    rw mem_compress at h₂,
    rcases h₂ with ⟨_, B, H, HB⟩ | _,
      rw ← HB at h₁,
      rw compress at HB h₁,
      split_ifs at HB h₁,
        rw mem_insert at h₁,
        rcases h₁ with rfl | h₁, tauto,
        exfalso, exact not_mem_erase _ _ h₁,
      rwa ← HB,
    tauto
  end

  lemma compress_both {𝒜 : finset (finset α)} {i j : α} {A : finset α} (h₁ : A ∈ compress_family i j 𝒜) (h₂ : j ∈ A) (h₃ : i ∉ A) : erase (insert i A) j ∈ 𝒜 :=
  begin
    have: A ∈ 𝒜, apply compress_held h₂ h₁, 
    rw mem_compress at h₁,
    replace h₁ : compress i j A ∈ 𝒜, tauto,
    rw compress at h₁,
    have: j ∈ A ∧ i ∉ A := ⟨h₂, h₃⟩,
    split_ifs at h₁,
    rwa ← insert_erase_comm,
    intro, rw a at *, tauto,
  end

  lemma compression_reduces_shadow {𝒜 : finset (finset α)} {i j : α} : (∂ compress_family i j 𝒜).card ≤ (∂𝒜).card := 
  begin
    set 𝒜' := compress_family i j 𝒜,
    suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
      suffices z: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
        rwa [sdiff_union_inter, sdiff_union_inter] at z,
      rw [card_disjoint_union, card_disjoint_union, inter_comm],
      apply add_le_add_right ‹_›,
      any_goals { apply sdiff_inter_inter },

    have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, i ∈ B ∧ j ∉ B ∧ erase (insert j B) i ∈ ∂𝒜 \ ∂𝒜',
      intros B HB,
      obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
      have m: ∀ y ∉ B, insert y B ∉ 𝒜,
        intros y _ _,
        apply k',
        rw mem_shadow',
        exact ⟨y, H, a⟩,
      rcases mem_shadow'.1 k with ⟨x, _, _⟩,
      have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
      rw insert.comm at q,
      have: j ∉ B := q.2.1 ∘ mem_insert_of_mem,
      have: i ≠ j, rintro rfl, tauto,
      have: x ≠ i, intro a, rw a at *, rw [erase_insert] at q, 
        exact m _ ‹j ∉ B› q.2.2,
        rw mem_insert, tauto,
      have: x ≠ j, intro a, rw a at q, exact q.2.1 (mem_insert_self _ _), 
      have: i ∈ B := mem_of_mem_insert_of_ne q.1 ‹x ≠ i›.symm,
      refine ⟨‹_›, ‹_›, _⟩,
      rw mem_sdiff,
      split,
        rw mem_shadow',
        rw ← insert_erase_comm ‹x ≠ i› at q,
        refine ⟨x, _, q.2.2⟩, 
        intro a, 
        exact ‹x ∉ B› (mem_of_mem_insert_of_ne (mem_of_mem_erase a) ‹x ≠ j›),

      intro a, rw mem_shadow' at a, 
      rcases a with ⟨y, yH, H⟩,
      have: y ≠ i, intro b, rw [b, insert_erase (mem_insert_of_mem ‹i ∈ B›)] at H, 
                  exact m _ ‹j ∉ B› (compress_held (mem_insert_self _ _) H), 
      have: y ≠ j, rw [mem_erase, mem_insert] at yH, tauto,
      have: y ∉ B, rw [mem_erase, mem_insert] at yH, tauto,
      have: j ∈ insert y (erase (insert j B) i), simp, tauto,
      have: i ∉ insert y (erase (insert j B) i), simp, tauto,
      have := compress_both H ‹_› ‹_›,
      rw [insert.comm, ← insert_erase_comm ‹y ≠ j›, insert_erase (mem_insert_of_mem ‹i ∈ B›), erase_insert ‹j ∉ B›] at this,
      exact m _ ‹y ∉ B› ‹insert y B ∈ 𝒜›,
    
    set f := (λ (B : finset α), erase (insert j B) i),
    apply card_le_card_of_inj_on f,
      intros _ HB,
      exact (q₁ _ HB).2.2,
  
    intros B₁ HB₁ B₂ HB₂ f₁,
    have z₁ := q₁ B₁ HB₁,
    have z₂ := q₁ B₂ HB₂,
    have: i ≠ j := by rintro rfl; tauto,
    rw ← insert_erase_comm ‹i ≠ j›.symm at z₁ z₂,
    apply inj_ish ⟨z₁.1, z₁.2.1⟩ ⟨z₂.1, z₂.2.1⟩, 
    convert f₁, all_goals {rw insert_erase_comm ‹i ≠ j›.symm}
  end
end
end ij

namespace UV
section 
  variables (U V : finset X)
  
  -- We'll only use this when |U| = |V| and U ∩ V = ∅
  def compress (U V : finset α) (A : finset α) :=
  if disjoint U A ∧ (V ⊆ A)
    then (A ∪ U) \ V
    else A

  -- local notation `C` := compress U V

  lemma compress_size (U V : finset α) (A : finset α) (h₁ : U.card = V.card) : (compress U V A).card = A.card :=
  begin
    rw compress, split_ifs, 
      rw [card_sdiff (subset.trans h.2 (subset_union_left _ _)), card_disjoint_union h.1.symm, h₁, nat.add_sub_cancel], 
    refl
  end

  lemma compress_idem (U V : finset α) (A : finset α) : compress U V (compress U V A) = compress U V A :=
  begin
    simp only [compress], 
    split_ifs,
        suffices: U = ∅,
          rw [this, union_empty, union_empty, sdiff_idem],
        have: U \ V = U := sdiff_eq_self_of_disjoint (disjoint_of_subset_right h.2 h.1),
        rw ← disjoint_self_iff_empty,
        apply disjoint_of_subset_right (subset_union_right (A\V) _),
        rw [union_sdiff_distrib_right, ‹U \ V = U›] at h_1,
    all_goals { tauto }
  end

  @[reducible]
  def compress_remains (U V : finset α) (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.filter (λ A, compress U V A ∈ 𝒜)
  @[reducible]
  def compress_motion (U V : finset α) (𝒜 : finset (finset α)) : finset (finset α) := (𝒜.filter (λ A, compress U V A ∉ 𝒜)).image (λ A, compress U V A)

  def compress_family (U V : finset α) (𝒜 : finset (finset α)) : finset (finset α) :=
  compress_motion U V 𝒜 ∪ compress_remains U V 𝒜

  local notation `CC` := compress_family U V

  lemma mem_compress_remains  {𝒜 : finset (finset α)} (U V : finset α) (A : finset α) : A ∈ compress_remains U V 𝒜 ↔ A ∈ 𝒜 ∧ compress U V A ∈ 𝒜 :=
  by rw mem_filter

  lemma mem_compress_motion {𝒜 : finset (finset α)} (U V : finset α) (A : finset α) : A ∈ compress_motion U V 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A) :=
  begin
    simp [compress_motion], 
    split; rintro ⟨p, q, r⟩,
      exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
    exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩, 
  end

  @[reducible]
  def is_compressed (U V : finset α) (𝒜 : finset (finset α)) : Prop := compress_family U V 𝒜 = 𝒜

  lemma is_compressed_empty (𝒜 : finset (finset α)) : is_compressed ∅ ∅ 𝒜 := 
  begin
    have q: ∀ (A : finset α), compress ∅ ∅ A = A,
      simp [compress],
    simp [is_compressed, compress_family, ext, q]
  end

  lemma mem_compress {𝒜 : finset (finset α)} (U V : finset α) {A : finset α} : 
    A ∈ compress_family U V 𝒜 ↔ (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A)) ∨ (A ∈ 𝒜 ∧ compress U V A ∈ 𝒜) :=
  by rw [compress_family, mem_union, mem_compress_remains, mem_compress_motion]

  lemma compress_family_size (r : ℕ) (𝒜 : finset (finset α)) (U V : finset α) (h₁ : U.card = V.card) (h₂ : is_layer 𝒜 r) : is_layer (compress_family U V 𝒜) r :=
  begin
    intros A HA,
    rw mem_compress at HA, 
    rcases HA with ⟨_, _, z₁, rfl⟩ | ⟨z₁, _⟩,
      rw compress_size _ _ _ h₁, 
    all_goals {apply h₂ _ z₁}
  end

  lemma compress_family_idempotent (U V : finset α) (𝒜 : finset (finset α)) : compress_family U V (compress_family U V 𝒜) = compress_family U V 𝒜 :=
  begin
    have: ∀ A ∈ compress_family U V 𝒜, compress U V A ∈ compress_family U V 𝒜,
      intros A HA,
      rw mem_compress at HA ⊢,
      simp [compress_idem], 
      rcases HA with ⟨_, B, _, rfl⟩ | ⟨_, _⟩,
        left, refine ⟨_, B, ‹_›, _⟩; rwa compress_idem,
      right, assumption,
    have: filter (λ A, compress U V A ∉ compress_family U V 𝒜) (compress_family U V 𝒜) = ∅,
      rw ← filter_false (compress_family U V 𝒜),
      apply filter_congr,
      simpa,
    rw [compress_family, compress_motion, this, image_empty, union_comm, compress_remains, ← this],
    apply filter_union_filter_neg_eq (compress_family U V 𝒜)
  end

  lemma compress_disjoint {𝒜 : finset (finset α)} (U V : finset α) : disjoint (compress_motion U V 𝒜) (compress_remains U V 𝒜) :=
  begin
    rw disjoint_left,
    intros A HA HB,
    rw mem_compress_remains at HB,
    rw mem_compress_motion at HA,
    exact HA.1 HB.1
  end

  lemma inj_ish {U V : finset α} {A B : finset α} (hA : disjoint U A ∧ V ⊆ A) (hB : disjoint U B ∧ V ⊆ B)
    (Z : (A ∪ U) \ V = (B ∪ U) \ V) : A = B :=
  begin
    ext x, split,
    all_goals {
      intro p,
      by_cases h₁: (x ∈ V), { exact hB.2 h₁ <|> exact hA.2 h₁ },
      have := mem_sdiff.2 ⟨mem_union_left U ‹_›, h₁⟩,
      rw Z at this <|> rw ← Z at this,
      rw [mem_sdiff, mem_union] at this,
      suffices: x ∉ U, tauto,
      apply disjoint_right.1 ‹disjoint _ _ ∧ _›.1 p }
  end

  lemma compressed_size {𝒜 : finset (finset α)} (U V : finset α) : (compress_family U V 𝒜).card = 𝒜.card :=
  begin
    rw [compress_family, card_disjoint_union (compress_disjoint _ _), card_image_of_inj_on],
      rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
      rw [disjoint_iff_inter_eq_empty, inter_comm],
      apply filter_inter_filter_neg_eq,
    intros A HA B HB Z,
    rw mem_filter at HA HB,
    rw compress at HA Z,
    split_ifs at HA Z,
      rw compress at HB Z,
      split_ifs at HB Z,
        exact inj_ish h h_1 Z,
      tauto,
    tauto
  end

  lemma compress_held {𝒜 : finset (finset α)} {U V : finset α} {A : finset α} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : V ⊆ A) (h₃ : U.card = V.card) : A ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
      rw compress at HB,
      split_ifs at HB,
        have: V = ∅,
          apply eq_empty_of_forall_not_mem,
          intros x xV, replace h₂ := h₂ xV, 
          rw [← HB, mem_sdiff] at h₂, exact h₂.2 xV,
        have: U = ∅,
          rwa [← card_eq_zero, h₃, card_eq_zero],
        rw [‹U = ∅›, ‹V = ∅›, union_empty, sdiff_empty] at HB,
        rwa ← HB, 
      rwa ← HB,
    tauto,
  end

  lemma compress_moved {𝒜 : finset (finset α)} {U V : finset α} {A : finset α} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : A ∉ 𝒜) : U ⊆ A ∧ disjoint V A ∧ (A ∪ V) \ U ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
    { rw compress at HB,
      split_ifs at HB, { 
        rw ← HB at *,
        refine ⟨_, disjoint_sdiff, _⟩,
          have: disjoint U V := disjoint_of_subset_right h.2 h.1,
          rw union_sdiff_distrib_right, rw sdiff_eq_self_of_disjoint this, apply subset_union_right _ _,
        rwa [sdiff_union_of_subset, union_sdiff_self, sdiff_eq_self_of_disjoint h.1.symm],
        apply trans h.2 (subset_union_left _ _)},
      { rw HB at *, tauto } },
    tauto
  end

  lemma uncompressed_was_already_there {𝒜 : finset (finset α)} {U V : finset α} {A : finset α} (h₁ : A ∈ compress_family U V 𝒜) (h₂ : V ⊆ A) (h₃ : disjoint U A) : (A ∪ U) \ V ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    have: disjoint U A ∧ V ⊆ A := ⟨h₃, h₂⟩,
    rcases h₁ with ⟨_, B, B_in_A, cB_eq_A⟩ | ⟨_, cA_in_A⟩,
    { by_cases a: (A ∪ U) \ V = A,
        have: U \ V = U := sdiff_eq_self_of_disjoint (disjoint_of_subset_right h₂ h₃),
        have: U = ∅,
          rw ← disjoint_self_iff_empty,
          suffices: disjoint U (U \ V), rw ‹U \ V = U› at this, assumption,
          apply disjoint_of_subset_right (subset_union_right (A\V) _),
          rwa [← union_sdiff_distrib_right, a],
        have: V = ∅,
          rw ← disjoint_self_iff_empty, apply disjoint_of_subset_right h₂,
          rw ← a, apply disjoint_sdiff,
        simpa [a, cB_eq_A.symm, compress, ‹U = ∅›, ‹V = ∅›],
      have: compress U V A = (A ∪ U) \ V,
        rw compress, split_ifs, refl,
      exfalso,
      apply a,
      rw [← this, ← cB_eq_A, compress_idem] },
    { rw compress at cA_in_A,
      split_ifs at cA_in_A,
      assumption }
  end

  lemma compression_reduces_shadow {𝒜 : finset (finset α)} {U V : finset α} (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜) (h₂ : U.card = V.card) : 
    (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := 
  begin
    set 𝒜' := CC 𝒜,
    suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
      suffices z: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
        rwa [sdiff_union_inter, sdiff_union_inter] at z,
      rw [card_disjoint_union, card_disjoint_union, inter_comm],
      apply add_le_add_right ‹_›,
      any_goals { apply sdiff_inter_inter },
    
    have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, U ⊆ B ∧ disjoint V B ∧ (B ∪ V) \ U ∈ ∂𝒜 \ ∂𝒜',
      intros B HB,
      obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
      have m: ∀ y ∉ B, insert y B ∉ 𝒜 := λ y H a, k' (mem_shadow'.2 ⟨y, H, a⟩),
      rcases mem_shadow'.1 k with ⟨x, _, _⟩,
      have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
      have: disjoint V B := (disjoint_insert_right.1 q.2.1).2,
      have: disjoint V U := disjoint_of_subset_right q.1 q.2.1,
      have: V \ U = V := sdiff_eq_self_of_disjoint ‹_›,
      have: x ∉ U,
        intro a, 
        rcases h₁ x ‹x ∈ U› with ⟨y, Hy, xy_comp⟩,
        apply m y (disjoint_left.1 ‹disjoint V B› Hy),
        rw is_compressed at xy_comp,
        have: (insert x B ∪ V) \ U ∈ compress_family (erase U x) (erase V y) 𝒜, rw xy_comp, exact q.2.2,
        have: ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y ∈ 𝒜,
          apply uncompressed_was_already_there this _ (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff),
            rw [union_sdiff_distrib_right, ‹V \ U = V›],
            apply subset.trans (erase_subset _ _) (subset_union_right _ _), 
        suffices: ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y = insert y B,
          rwa ← this,
        have: x ∉ B ∪ V := λ z, disjoint_left.1 ‹disjoint V U› (or.resolve_left (mem_union.1 z) ‹x ∉ B›) ‹x ∈ U›,
        have: erase U x ⊆ insert x B ∪ V := (trans (erase_subset x _) (trans q.1 (subset_union_left _ V))),
        by calc (((insert x B ∪ V) \ U) ∪ erase U x) \ erase V y 
            = (((insert x B ∪ V) \ finset.singleton x ∪ erase U x) ∩ ((insert x B ∪ V) \ erase U x ∪ erase U x)) \ erase V y : 
                                  by rw [← union_distrib_right, ← sdiff_union_distrib_left, union_singleton_eq_insert, insert_erase a]
        ... = (B ∪ V) \ erase V y : 
                                  by rw [sdiff_union_of_subset ‹erase U x ⊆ _›, sdiff_singleton_eq_erase, insert_union, erase_insert ‹x ∉ B ∪ V›, ← union_singleton_eq_insert, union_comm, ← union_distrib_right, inter_singleton_of_not_mem (not_mem_erase _ _), empty_union]
        ... = (insert y B ∪ erase V y) \ erase V y :  
                                  by rw [← union_singleton_eq_insert, union_comm _ B, union_assoc, union_singleton_eq_insert, insert_erase ‹y ∈ V›]
        ... = insert y B : 
                                  begin rw [union_sdiff_self, sdiff_eq_self_iff_disjoint, disjoint_insert_left], refine ⟨not_mem_erase _ _, disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm⟩ end,                 
      have: U ⊆ B, rw [← erase_eq_of_not_mem ‹x ∉ U›, ← subset_insert_iff], exact q.1,
      refine ⟨‹_›, ‹_›, _⟩,
      rw mem_sdiff,
      have: x ∉ V := disjoint_right.1 q.2.1 (mem_insert_self _ _),
      split,
        rw mem_shadow',
        refine ⟨x, _, _⟩,
        { simp [mem_sdiff, mem_union], tauto! },
        convert q.2.2,
        rw [← union_singleton_eq_insert, ← union_singleton_eq_insert, union_assoc, union_sdiff_distrib_right _ (B ∪ V), sdiff_eq_self_of_disjoint (singleton_disjoint.2 ‹x ∉ U›)], 
      rw mem_shadow',
      rintro ⟨w, _, _⟩,
      by_cases (w ∈ U),
        rcases h₁ w ‹w ∈ U› with ⟨z, Hz, xy_comp⟩,
        apply m z (disjoint_left.1 ‹disjoint V B› Hz),
        have: insert w ((B ∪ V) \ U) ∈ 𝒜, {
          apply compress_held a_h_h _ h₂, 
          apply subset.trans _ (subset_insert _ _),
          rw union_sdiff_distrib_right, rw ‹V \ U = V›, apply subset_union_right },
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z ∈ 𝒜,
          refine uncompressed_was_already_there _ _ _, 
              rw is_compressed at xy_comp,
              rwa xy_comp,
            apply subset.trans (erase_subset _ _),
            apply subset.trans _ (subset_insert _ _),
            rw union_sdiff_distrib_right,
            rw ‹V \ U = V›,
            apply subset_union_right,
          rw disjoint_insert_right,
          split, apply not_mem_erase,
          apply disjoint_of_subset_left (erase_subset _ _),
          apply disjoint_sdiff,
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = insert z B,
        by calc (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = (((B ∪ V) \ U) ∪ (finset.singleton w ∪ erase U w)) \ erase V z : begin rw [← union_singleton_eq_insert, union_left_comm, union_assoc] end
        ... = (((B ∪ V) \ U) ∪ U) \ erase V z : begin congr, rw union_singleton_eq_insert, rw insert_erase h end
        ... = (B ∪ V) \ erase V z : begin rw sdiff_union_of_subset, apply subset.trans ‹U ⊆ B› (subset_union_left _ _) end
        ... = B \ erase V z ∪ V \ erase V z : begin rw union_sdiff_distrib_right end
        ... = B ∪ V \ erase V z : begin congr, rw sdiff_eq_self_iff_disjoint, apply disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm end
        ... = B ∪ finset.singleton z : begin congr, ext, simp, split, intro p, by_contra, exact p.2 ‹_› p.1, intro p, rw p, tauto end
        ... = insert z B : begin rw [union_comm, union_singleton_eq_insert] end,
        rwa ← this,
      rw [mem_sdiff, ← not_imp, not_not] at a_h_w,
      have: w ∉ V := h ∘ a_h_w ∘ mem_union_right _,
      have: w ∉ B := h ∘ a_h_w ∘ mem_union_left _,
      apply m w this,
      
      have: (insert w ((B ∪ V) \ U) ∪ U) \ V ∈ 𝒜, 
        refine uncompressed_was_already_there ‹insert w ((B ∪ V) \ U) ∈ 𝒜'› (trans _ (subset_insert _ _)) _,
          rw [union_sdiff_distrib_right, ‹V \ U = V›], apply subset_union_right,
          rw disjoint_insert_right,
          exact ⟨‹_›, disjoint_sdiff⟩,
      convert this,
      rw [insert_union, sdiff_union_of_subset (trans ‹U ⊆ B› (subset_union_left _ _)), ← insert_union, union_sdiff_self], symmetry,
      rw [sdiff_eq_self_iff_disjoint, disjoint_insert_left],
      split, assumption,
      rwa disjoint.comm,
    apply card_le_card_of_inj_on (λ B, (B ∪ V) \ U) (λ B HB, (q₁ B HB).2.2),
    intros B₁ HB₁ B₂ HB₂ k,
    exact inj_ish ⟨(q₁ B₁ HB₁).2.1, (q₁ B₁ HB₁).1⟩ ⟨(q₁ B₂ HB₂).2.1, (q₁ B₂ HB₂).1⟩ k
  end

  def bin_measure (A : finset X) : ℕ := A.sum (λ x, pow 2 x.val)

  lemma binary_sum (k : ℕ) (A : finset ℕ) (h₁ : ∀ x ∈ A, x < k) : A.sum (pow 2) < 2^k :=
  begin
    apply lt_of_le_of_lt (sum_le_sum_of_subset (λ t th, mem_range.2 (h₁ t th))),
    have z := geom_sum_mul_add 1 k, rw [geom_series, mul_one] at z, 
    simp only [nat.pow_eq_pow] at z, rw ← z, apply nat.lt_succ_self
  end

  lemma binary_sum' (k : ℕ) (A : finset X) (h₁ : ∀ (x : X), x ∈ A → x.val < k) : bin_measure A < 2^k :=
  begin
    suffices: bin_measure A = (A.image (λ (x : X), x.val)).sum (pow 2),
      rw this, apply binary_sum, intros t th, rw mem_image at th, rcases th with ⟨_, _, _⟩,
      rw ← th_h_h, apply h₁ _ th_h_w, 
    rw [bin_measure, sum_image], intros x _ y _, exact fin.eq_of_veq,
  end

  lemma bin_lt_of_maxdiff (A B : finset X) : (∃ (k : X), k ∉ A ∧ k ∈ B ∧ (∀ (x : X), k < x → (x ∈ A ↔ x ∈ B))) → bin_measure A < bin_measure B :=
  begin
    rintro ⟨k, notinA, inB, maxi⟩,
    have AeqB: A.filter (λ x, ¬(x ≤ k)) = B.filter (λ x, ¬(x ≤ k)),
    { ext t, rw [mem_filter, mem_filter], 
      by_cases h: (k < t); simp [h], 
      apply maxi, exact h },
    { have Alt: (A.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val) < pow 2 k.1,
        rw ← bin_measure, apply binary_sum', intro t, rw mem_filter, intro b, 
        cases lt_or_eq_of_le b.2, exact h, rw h at b, exfalso, exact notinA b.1,
      have leB: pow 2 k.1 ≤ (B.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val),
        apply @single_le_sum _ _ (B.filter (λ x, x ≤ k)) (λ (x : fin n), 2 ^ x.val) _ _ (λ x _, nat.zero_le _) k,
        rw mem_filter, exact ⟨inB, le_refl _⟩, 
      have AltB: (A.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val) < (B.filter (λ x, x ≤ k)).sum (λ x, pow 2 x.val) := lt_of_lt_of_le Alt leB,
      have := nat.add_lt_add_right AltB (sum (filter (λ (x : fin n), ¬(x ≤ k)) A) (λ (x : fin n), 2 ^ x.val)), 
      rwa [← sum_union, filter_union_filter_neg_eq, AeqB, ← sum_union, filter_union_filter_neg_eq, ← bin_measure, ← bin_measure] at this,
      rw disjoint_iff_inter_eq_empty, apply filter_inter_filter_neg_eq,
      rw disjoint_iff_inter_eq_empty, apply filter_inter_filter_neg_eq }
  end

  lemma bin_iff (A B : finset X) : bin_measure A < bin_measure B ↔ ∃ (k : X), k ∉ A ∧ k ∈ B ∧ (∀ (x : X), k < x → (x ∈ A ↔ x ∈ B)) := 
  begin
    split, 
      intro p,
      set differ := univ.filter (λ x, ¬ (x ∈ A ↔ x ∈ B)),
      have h: differ ≠ ∅,
        intro q, suffices: A = B, rw this at p, exact irrefl _ p,
        ext a, by_contra z, have: differ ≠ ∅ := ne_empty_of_mem (mem_filter.2 ⟨complete _, z⟩), 
        exact this q,
      set k := max' differ h, use k,
      have z: ∀ (x : fin n), k < x → (x ∈ A ↔ x ∈ B),
        intros t th, by_contra, apply not_le_of_gt th, apply le_max', simpa [complete], 
      rw ← and.rotate, refine ⟨z, _⟩,
      have el: (k ∈ A ∧ k ∉ B) ∨ (k ∉ A ∧ k ∈ B),
        have := max'_mem differ h, rw mem_filter at this, tauto,
      apply or.resolve_left el,
      intro, apply not_lt_of_gt p (bin_lt_of_maxdiff B A ⟨k, a.2, a.1, λ x xh, (z x xh).symm⟩), 
    exact bin_lt_of_maxdiff _ _,
  end

  -- here
  lemma bin_measure_inj (A B : finset X) : bin_measure A = bin_measure B → A = B :=
  begin
    intro p, set differ := univ.filter (λ x, ¬ (x ∈ A ↔ x ∈ B)),
    by_cases h: (differ = ∅),
      ext a, by_contra z, have: differ ≠ ∅ := ne_empty_of_mem (mem_filter.2 ⟨complete _, z⟩), 
      exact this h,
    set k := max' differ h,
    have el: (k ∈ A ∧ k ∉ B) ∨ (k ∉ A ∧ k ∈ B),
      have := max'_mem differ h, rw mem_filter at this, tauto,
    exfalso,
    cases el,
      apply not_le_of_gt ((bin_iff B A).2 ⟨k, el.2, el.1, _⟩) (le_of_eq p), swap,
      apply not_le_of_gt ((bin_iff A B).2 ⟨k, el.1, el.2, _⟩) (ge_of_eq p), 
    all_goals { intros x xh, by_contra, apply not_le_of_gt xh, apply le_max', simp only [mem_univ, true_and, mem_filter], tauto }, 
  end

  def c_measure (𝒜 : finset (finset X)) : ℕ := 𝒜.sum bin_measure

  lemma compression_reduces_bin_measure {U V : finset X} (hU : U ≠ ∅) (hV : V ≠ ∅) (A : finset X) (h : max' U hU < max' V hV) : compress U V A ≠ A → bin_measure (compress U V A) < bin_measure A :=
  begin
    intro a,
    rw compress at a ⊢,
    split_ifs at a ⊢,
    { rw bin_measure, rw bin_measure,
      rw ← add_lt_add_iff_right,
        have q : V ⊆ (A ∪ U) := trans h_1.2 (subset_union_left _ _),
        rw sum_sdiff q,
      rw [sum_union h_1.1.symm, add_lt_add_iff_left],
      set kV := (max' V hV).1,
      set kU := (max' U hU).1,
      have a3: 2^kV ≤ sum V (λ (x : fin n), pow 2 x.val) := @single_le_sum _ _ V (λ x, pow 2 x.val) _ _ (λ t _, nat.zero_le _) _ (max'_mem V hV),
      have a1: sum U (λ (x : fin n), 2 ^ x.val) < 2^(kU+1), 
        { rw ← bin_measure, apply binary_sum', intros x hx, rw nat.lt_succ_iff, apply le_max' U _ _ hx },
      have a2: kU + 1 ≤ kV, exact h,
      apply lt_of_lt_of_le a1,
      transitivity (2^kV), rwa nat.pow_le_iff_le_right (le_refl 2),
      assumption },
    { exfalso, apply a, refl }
  end

  lemma compression_reduces_measure (U V : finset X) (hU : U ≠ ∅) (hV : V ≠ ∅) (h : max' U hU < max' V hV) (𝒜 : finset (finset X)) : compress_family U V 𝒜 ≠ 𝒜 → c_measure (compress_family U V 𝒜) < c_measure 𝒜 :=
  begin
    rw [compress_family], intro, 
    rw [c_measure, c_measure, sum_union (compress_disjoint U V)],
    conv {to_rhs, rw ← @filter_union_filter_neg_eq _ (λ A, compress U V A ∈ 𝒜) _ _ 𝒜, rw sum_union (disjoint_iff_inter_eq_empty.2 (filter_inter_filter_neg_eq _)) },
    rw [add_comm, add_lt_add_iff_left, sum_image],
      apply sum_lt_sum,
      { intro a₁,
        rw [compress_motion, compress_remains, a₁, image_empty, empty_union] at a,
        apply a,
        conv_rhs {rw ← @filter_union_filter_neg_eq _ (λ A, compress U V A ∈ 𝒜) _ _ 𝒜}, conv {to_lhs, rw ← union_empty (filter _ 𝒜)},
        symmetry,
        rw ← a₁ },
      intros A HA,
      apply compression_reduces_bin_measure _ _ _ h,
      intro a₁, rw [mem_filter, a₁] at HA,
      tauto,
    intros x Hx y Hy k,
    rw mem_filter at Hx Hy,
    have cx: compress U V x ≠ x, intro b, rw b at Hx, tauto,
    have cy: compress U V y ≠ y, intro b, rw b at Hy, tauto,
    rw compress at k Hx cx, split_ifs at k Hx cx,
      rw compress at k Hy cy, split_ifs at k Hy cy,
        exact inj_ish h_1 h_2 k,
      tauto,
    tauto,
  end

  def gamma : rel (finset X) (finset X) := (λ U V, ∃ (HU : U ≠ ∅), ∃ (HV : V ≠ ∅), disjoint U V ∧ finset.card U = finset.card V ∧ max' U HU < max' V HV)

  lemma compression_improved {r : ℕ} (U V : finset X) (𝒜 : finset (finset X)) (h : is_layer 𝒜 r) (h₁ : gamma U V) 
    (h₂ : ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ 𝒜) (h₃ : ¬ is_compressed U V 𝒜): 
    c_measure (compress_family U V 𝒜) < c_measure 𝒜 ∧ (compress_family U V 𝒜).card = 𝒜.card ∧ is_layer (compress_family U V 𝒜) r ∧ (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card := 
  begin
    rcases h₁ with ⟨Uh, Vh, UVd, same_size, max_lt⟩,
    refine ⟨compression_reduces_measure U V Uh Vh max_lt _ h₃, compressed_size _ _, _, _⟩,
    apply' compress_family_size _ _ _ _ same_size h, 
    apply compression_reduces_shadow _ same_size,
    intros x Hx, refine ⟨min' V Vh, min'_mem _ _, _⟩,
    cases lt_or_le 1 U.card with p p,
    { apply h₂,
      refine ⟨⟨_, _, _, _, _⟩, card_erase_lt_of_mem Hx⟩,
      { rwa [← card_pos, card_erase_of_mem Hx, nat.lt_pred_iff] },
      { rwa [← card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, nat.lt_pred_iff] },
      { apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_of_subset_right (erase_subset _ _), assumption },
      { rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size] },
      { have: max' (erase U _) _ ≤ max' U Uh := max'_le _ _ _ (λ y Hy, le_max' _ Uh _ (mem_of_mem_erase Hy)),
        apply lt_of_le_of_lt this,
        apply lt_of_lt_of_le max_lt,
        apply le_max',
        rw mem_erase,
        refine ⟨_, max'_mem _ _⟩,
        intro,
        rw same_size at p,
        apply not_le_of_lt p,
        apply le_of_eq,
        rw card_eq_one,
        use max' V Vh,
        rw eq_singleton_iff_unique_mem,
        refine ⟨max'_mem _ _, λ t Ht, _⟩,
        apply le_antisymm,
          apply le_max' _ _ _ Ht,
        rw a, apply min'_le _ _ _ Ht } },
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

  instance thing (U V : finset X) : decidable (gamma U V) := by rw gamma; apply_instance
  instance thing2 (U V : finset X) (A : finset (finset X)) : decidable (is_compressed U V A) := by rw is_compressed; apply_instance

  lemma kruskal_katona_helper (r : ℕ) (𝒜 : finset (finset X)) (h : is_layer 𝒜 r) : 
    ∃ (ℬ : finset (finset X)), (∂ℬ).card ≤ (∂𝒜).card ∧ 𝒜.card = ℬ.card ∧ is_layer ℬ r ∧ (∀ U V, gamma U V → is_compressed U V ℬ) := 
  begin
    refine @well_founded.recursion _ _ (measure_wf c_measure) (λ (A : finset (finset X)), is_layer A r → ∃ B, (∂B).card ≤ (∂A).card ∧ A.card = B.card ∧ is_layer B r ∧ ∀ (U V : finset X), gamma U V → is_compressed U V B) _ _ h,
    intros A ih z,
    set usable: finset (finset X × finset X) := filter (λ t, gamma t.1 t.2 ∧ ¬ is_compressed t.1 t.2 A) ((powerset univ).product (powerset univ)), 
    by_cases (usable = ∅),
      refine ⟨A, le_refl _, rfl, z, _⟩, intros U V k,
      rw eq_empty_iff_forall_not_mem at h,
      by_contra,
      apply h ⟨U,V⟩,
      simp [a, k], exact ⟨subset_univ _, subset_univ _⟩,
    rcases exists_min usable (λ t, t.1.card) ((nonempty_iff_ne_empty _).2 h) with ⟨⟨U,V⟩, uvh, t⟩, rw mem_filter at uvh,
    have h₂: ∀ U₁ V₁, gamma U₁ V₁ ∧ U₁.card < U.card → is_compressed U₁ V₁ A,
      intros U₁ V₁ h, by_contra, 
      apply not_le_of_gt h.2 (t ⟨U₁, V₁⟩ _),
      simp [h, a], exact ⟨subset_univ _, subset_univ _⟩,
    obtain ⟨small_measure, p2, layered, p1⟩ := compression_improved U V A z uvh.2.1 h₂ uvh.2.2, 
    rw [measure, inv_image] at ih, 
    rcases ih (compress_family U V A) small_measure layered with ⟨B, q1, q2, q3, q4⟩,
    exact ⟨B, trans q1 p1, trans p2.symm q2, q3, q4⟩
  end

  def binary : finset X → finset X → Prop := inv_image (<) bin_measure
  local infix ` ≺ `:50 := binary

  instance : is_trichotomous (finset X) binary := ⟨
    begin
      intros A B,
      rcases lt_trichotomy (bin_measure A) (bin_measure B) with lt|eq|gt,
      { left, exact lt },
      { right, left, exact bin_measure_inj A B eq },
      { right, right, exact gt }
    end
  ⟩

  def is_init_seg_of_colex (𝒜 : finset (finset X)) (r : ℕ) : Prop := is_layer 𝒜 r ∧ (∀ A ∈ 𝒜, ∀ B, B ≺ A ∧ B.card = r → B ∈ 𝒜)

  lemma init_seg_total (𝒜₁ 𝒜₂ : finset (finset X)) (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜₁ r) (h₂ : is_init_seg_of_colex 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ :=
  begin
    rw ← sdiff_eq_empty_iff_subset, rw ← sdiff_eq_empty_iff_subset,
    by_contra a, rw not_or_distrib at a, simp [exists_mem_iff_ne_empty.symm, exists_mem_iff_ne_empty.symm] at a,
    rcases a with ⟨⟨A, Ah₁, Ah₂⟩, ⟨B, Bh₁, Bh₂⟩⟩,
    rcases trichotomous_of binary A B with lt | eq | gt,
      { exact Ah₂ (h₂.2 B Bh₁ A ⟨lt, h₁.1 A Ah₁⟩) },
      { rw eq at Ah₁, exact Bh₂ Ah₁ },
      { exact Bh₂ (h₁.2 A Ah₁ B ⟨gt, h₂.1 B Bh₁⟩) },
  end

  lemma init_seg_of_compressed (ℬ : finset (finset X)) (r : ℕ) (h₁ : is_layer ℬ r) (h₂ : ∀ U V, gamma U V → is_compressed U V ℬ): 
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
        { exfalso, have z := compression_reduces_bin_measure hV hU A gt, rw cA_eq_B at z,
          apply irrefl (bin_measure B) (trans (z ‹A ≠ B›.symm) A_lt_B)
        },
      },
    have: gamma U V,
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

  lemma exists_max {α β : Type*} [decidable_linear_order α] (s : finset β) (f : β → α)
    (h : s ≠ ∅) : ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
  begin
    have : s.image f ≠ ∅,
      rwa [ne, image_eq_empty, ← ne.def],
    cases max_of_ne_empty this with y hy,
    rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩,
    exact ⟨x, hx, λ x' hx', le_max_of_mem (mem_image_of_mem f hx') hy⟩,
  end

  def everything_up_to (A : finset X) : finset (finset X) := filter (λ (B : finset X), A.card = B.card ∧ bin_measure B ≤ bin_measure A) (powerset univ)

  lemma mem_everything_up_to (A : finset X) (B : finset X) : B ∈ everything_up_to A ↔ card A = card B ∧ bin_measure B ≤ bin_measure A :=
  begin
    rw everything_up_to, rw mem_filter, rw mem_powerset, split, tauto, 
    rintro ⟨a₁, a₂⟩, refine ⟨subset_univ _, a₁, a₂⟩,
  end

  lemma IS_iff_le_max (𝒜 : finset (finset X)) (r : ℕ) : 𝒜 ≠ ∅ ∧ is_init_seg_of_colex 𝒜 r ↔ ∃ (A : finset X), A ∈ 𝒜 ∧ A.card = r ∧ 𝒜 = everything_up_to A := 
  begin
    rw is_init_seg_of_colex, split, 
    { rintro ⟨ne, layer, IS⟩,
      rcases exists_max 𝒜 bin_measure ne with ⟨A, Ah, Ap⟩,
      refine ⟨A, Ah, layer A Ah, _⟩,
      ext B, rw [mem_everything_up_to], split; intro p,
        refine ⟨_, _⟩,
          convert layer A Ah, apply layer B p, 
        apply Ap _ p, 
      cases lt_or_eq_of_le p.2 with h h,
        apply IS A Ah B ⟨h, trans p.1.symm (layer A Ah)⟩, 
      rwa (bin_measure_inj _ _ h), 
    },
    { rintro ⟨A, Ah, Ac, Ap⟩,
      refine ⟨ne_empty_of_mem Ah, _, _⟩,
        intros B Bh, rw [Ap, mem_everything_up_to] at Bh, exact (trans Bh.1.symm Ac),
      intros B₁ Bh₁ B₂ Bh₂, rw [Ap, mem_everything_up_to], refine ⟨trans Ac Bh₂.2.symm, _⟩,
      { rw [binary, inv_image] at Bh₂, transitivity, apply le_of_lt Bh₂.1, rw [Ap, mem_everything_up_to] at Bh₁, exact Bh₁.2 }
    }
  end

  lemma up_to_is_IS {A : finset X} {r : ℕ} (h₁ : A.card = r) : is_init_seg_of_colex (everything_up_to A) r := 
  and.right $ (IS_iff_le_max _ _).2 
  (by refine ⟨A, _, h₁, rfl⟩; rw [mem_everything_up_to]; refine ⟨rfl, le_refl _⟩)

  lemma shadow_of_everything_up_to (A : finset X) (hA : A ≠ ∅) : ∂ (everything_up_to A) = everything_up_to (erase A (min' A hA)) :=
  begin
    ext B, split, 
      rw [mem_shadow', mem_everything_up_to], rintro ⟨i, ih, p⟩,
      rw [mem_everything_up_to, card_insert_of_not_mem ih] at p, 
      have cards: card (erase A (min' A hA)) = card B,
        rw [card_erase_of_mem (min'_mem _ _), p.1], refl,
      refine ⟨cards, _⟩, 
      cases lt_or_eq_of_le p.2 with h h,
      { rw bin_iff at h, rcases h with ⟨k, knotin, kin, h⟩,
        have: k ≠ i, rw mem_insert at knotin, tauto,
        cases lt_or_gt_of_ne this with h₁ h₁,
        { have q: i ∈ A := (h _ h₁).1 (mem_insert_self _ _), 
          apply le_of_lt, rw bin_iff,
          refine ⟨i, ih, _, _⟩,
            apply mem_erase_of_ne_of_mem (ne_of_gt _) q,
            apply lt_of_le_of_lt (min'_le _ _ _ kin) h₁, 
          intros x hx, have z := trans h₁ hx, have := h _ z, simp only [mem_insert, mem_erase, ne.def] at this ⊢, 
          have a1: ¬x = min' A hA := ne_of_gt (lt_of_le_of_lt (min'_le _ hA _ q) hx), 
          have a2: ¬x = i := ne_of_gt hx, tauto }, 
        { rcases lt_or_eq_of_le (min'_le _ hA _ kin) with h_1 | rfl,
            apply le_of_lt, rw bin_iff,
            refine ⟨k, mt mem_insert_of_mem knotin, mem_erase_of_ne_of_mem (ne_of_gt h_1) kin, _⟩,
            intros x hx, have := h _ hx, simp only [mem_insert, mem_erase, ne.def] at this ⊢,
            have a1: ¬x = min' A hA := ne_of_gt (lt_of_le_of_lt (min'_le _ hA _ kin) hx), 
            have a2: ¬x = i := ne_of_gt (trans hx h₁), tauto, 
          apply ge_of_eq, congr,
          apply eq_of_subset_of_card_le _ (ge_of_eq cards), 
          intros t th, rw mem_erase at th, 
          have: min' A hA < t, apply lt_of_le_of_ne (min'_le _ _ _ th.2) th.1.symm, 
          apply mem_of_mem_insert_of_ne ((h t this).2 th.2) (ne_of_gt (trans this h₁)) } },
      { replace h := bin_measure_inj _ _ h,
        have z: i ∈ A, rw ← h, exact mem_insert_self _ _,
        rw [bin_measure, bin_measure, ← sdiff_singleton_eq_erase], 
        rw ← add_le_add_iff_right (sum (finset.singleton i) (λ (x : fin n), 2 ^ x.val)), 
        rw [← sum_union (disjoint_singleton.2 ih), union_comm, union_singleton_eq_insert, h], 
        rw ← sum_sdiff (show finset.singleton (min' A hA) ⊆ A, by intro t; simp; intro th; rw th; exact min'_mem _ _), 
        rw [add_le_add_iff_left, sum_singleton, sum_singleton], apply nat.pow_le_pow_of_le_right zero_lt_two,
        exact min'_le _ _ _ z },
    intro p,
    rw [mem_everything_up_to] at p,
    simp only [mem_shadow', mem_everything_up_to], 
    cases eq_or_lt_of_le p.2,
      { rw bin_measure_inj _ _ h, refine ⟨min' A hA, not_mem_erase _ _, _⟩, rw insert_erase (min'_mem _ _), simp [le_refl] },
    rw bin_iff at h, rcases h with ⟨k, knotin, kin, h⟩,
    have kincomp := mem_sdiff.2 ⟨mem_univ _, knotin⟩,
    have jex: univ \ B ≠ ∅ := ne_empty_of_mem (mem_sdiff.2 ⟨mem_univ _, knotin⟩),
    set j := min' (univ \ B) jex,
    have jnotin: j ∉ B,
      have: j ∈ univ \ B := min'_mem _ _, rw mem_sdiff at this, tauto,
    have cards: card A = card (insert j B),
    { rw [card_insert_of_not_mem jnotin, ← p.1, card_erase_of_mem (min'_mem _ _), nat.pred_eq_sub_one, nat.sub_add_cancel], 
      apply nat.pos_of_ne_zero, rw ne, rw card_eq_zero, exact hA },
    refine ⟨j, jnotin, cards, _⟩,
    cases eq_or_lt_of_le (min'_le _ jex _ kincomp) with h₁ h_1, 
    { have: j = k, rw ← h₁, rw this at *, clear jnotin this j,
      suffices: insert k B = A, apply le_of_eq, rw this, symmetry, 
      apply eq_of_subset_of_card_le, 
      { intros t th, rcases lt_trichotomy t k with lt | rfl | gt,
        { apply mem_insert_of_mem, by_contra, have: t ∈ univ \ B, simpa, apply not_le_of_lt lt, rw ← h₁, apply min'_le _ _ _ this },
        { apply mem_insert_self },
        { apply mem_insert_of_mem, rw (h t gt), rw mem_erase, refine ⟨_, th⟩, apply ne_of_gt, apply lt_of_le_of_lt _ gt, apply min'_le, apply mem_of_mem_erase kin } }, 
      { apply le_of_eq cards.symm } }, 
    { apply le_of_lt, rw bin_iff, refine ⟨k, _, _, _⟩, 
      { rw [mem_insert], have: j ≠ k := ne_of_lt h_1, tauto },
      exact mem_of_mem_erase kin, intros x xh, have use := h x xh, 
      have: x ≠ min' A hA := ne_of_gt (lt_of_le_of_lt (min'_le _ _ _ (mem_of_mem_erase kin)) xh),
      have: x ≠ j := ne_of_gt (trans xh h_1),
      simp at use ⊢, tauto }
  end

  lemma shadow_of_IS {𝒜 : finset (finset X)} (r : ℕ) (h₁ : is_init_seg_of_colex 𝒜 r) : is_init_seg_of_colex (∂𝒜) (r - 1) :=
  begin
    rcases nat.eq_zero_or_pos r with rfl | hr,
      have: 𝒜 ⊆ finset.singleton ∅,
        intros A hA, rw mem_singleton, rw ← card_eq_zero, apply h₁.1 A hA,  
      have := bind_sub_bind_of_sub_left all_removals this, simp [all_removals, shadow, subset_empty] at this,
      simp [shadow, this, is_init_seg_of_colex, is_layer],
    by_cases h₂: 𝒜 = ∅,
      simp [h₂, shadow, is_init_seg_of_colex, is_layer],
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

#eval UV.everything_up_to ({2,4,5} : finset (fin 6))

section KK
  theorem kruskal_katona (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    is_layer 𝒜 r ∧ is_layer 𝒞 r ∧ 𝒜.card = 𝒞.card ∧ UV.is_init_seg_of_colex 𝒞 r 
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

  theorem strengthened (r : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    is_layer 𝒜 r ∧ is_layer 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (∂𝒞).card ≤ (∂𝒜).card :=
  begin
    rintros ⟨Ar, Cr, cards, colex⟩,
    rcases exists_smaller_set 𝒜 𝒞.card cards with ⟨𝒜', prop, size⟩,
    have := kruskal_katona r 𝒜' 𝒞 ⟨λ A hA, Ar _ (prop hA), Cr, size, colex⟩,
    transitivity, exact this, apply card_le_of_subset, rw [shadow, shadow], apply bind_sub_bind_of_sub_left _ prop
  end

  theorem iterated (r k : ℕ) (𝒜 𝒞 : finset (finset X)) : 
    is_layer 𝒜 r ∧ is_layer 𝒞 r ∧ 𝒞.card ≤ 𝒜.card ∧ UV.is_init_seg_of_colex 𝒞 r 
  → (shadow^[k] 𝒞).card ≤ (shadow^[k] 𝒜).card :=
  begin
    revert r 𝒜 𝒞, induction k,
      intros, simp, exact a.2.2.1,
    rintros r A C ⟨z₁, z₂, z₃, z₄⟩, simp, apply k_ih (r-1), refine ⟨shadow_layer z₁, shadow_layer z₂, _, _⟩,
    apply strengthened r _ _ ⟨z₁, z₂, z₃, z₄⟩, 
    apply UV.shadow_of_IS _ z₄
  end

  theorem lovasz_form {r k i : ℕ} {𝒜 : finset (finset X)} (hir : i ≤ r) (hrk : r ≤ k) (hkn : k ≤ n) (h₁ : is_layer 𝒜 r) (h₂ : nat.choose k r ≤ 𝒜.card) : 
    nat.choose k (r-i) ≤ (shadow^[i] 𝒜).card :=
  begin
    set range'k : finset X := attach_fin (range k) (λ m, by rw mem_range; apply forall_lt_iff_le.2 hkn),
    set 𝒞 : finset (finset X) := powerset_len r (range'k),
    have Ccard: 𝒞.card = nat.choose k r,
      rw [card_powerset_len, card_attach_fin, card_range], 
    have: is_layer 𝒞 r, intros A HA, rw mem_powerset_len at HA, exact HA.2,
    suffices this: (shadow^[i] 𝒞).card = nat.choose k (r-i),
    { rw ← this, apply iterated r _ _ _ ⟨h₁, ‹is_layer 𝒞 r›, _, _⟩, 
      rwa Ccard, 
      refine ⟨‹_›, _⟩, rintros A HA B ⟨HB₁, HB₂⟩, 
      rw mem_powerset_len, refine ⟨_, ‹_›⟩, 
      intros t th, rw mem_attach_fin, rw mem_range, 
      by_contra, simp at a, 
      rw [UV.binary, inv_image] at HB₁,
      apply not_le_of_gt HB₁, 
      transitivity 2^k,
        apply le_of_lt, 
        apply UV.binary_sum',
        intros x hx, rw mem_powerset_len at HA, exact mem_range.1 ((mem_attach_fin _).1 (HA.1 hx)), 
      have: (λ (x : X), 2^x.val) t ≤ _ := single_le_sum _ th, 
        transitivity, apply nat.pow_le_pow_of_le_right zero_lt_two a, rwa UV.bin_measure,
      intros _ _, apply nat.zero_le },
    suffices: (shadow^[i] 𝒞) = powerset_len (r-i) range'k,
      rw [this, card_powerset_len, card_attach_fin, card_range], 
    ext B, rw mem_powerset_len, rw sub_iff_shadow_iter, 
    split, 
      rintro ⟨A, Ah, BsubA, card_sdiff_i⟩,
      rw mem_powerset_len at Ah, refine ⟨trans BsubA Ah.1, _⟩, symmetry,
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

def intersecting (𝒜 : finset (finset X)) : Prop := ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ¬ disjoint A B

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
  have: (λ (u : finset X), card (f u)) =  (λ _, 2),
    funext, rw card_insert_of_not_mem, rw card_singleton, rw mem_singleton, 
    intro, simp [ext] at a, apply a, exact ⟨0, hn⟩,
  rw this at q, rw sum_const at q, rw nat.smul_eq_mul at q, 
  rw ← nat.le_div_iff_mul_le' zero_lt_two at q, 
  conv_rhs at q {rw ← nat.sub_add_cancel hn},
  rw nat.pow_add at q, simp at q, assumption,
end

def extremal_intersecting (hn : 1 ≤ n) : finset (finset X) :=
(powerset univ).filter (λ A, (⟨0, hn⟩: X) ∈ A)

theorem EKR {𝒜 : finset (finset X)} {r : ℕ} (h₁ : intersecting 𝒜) (h₂ : is_layer 𝒜 r) (h₃ : r < n/2) : 𝒜.card ≤ nat.choose (n-1) (r-1) :=
begin
  cases nat.eq_zero_or_pos r with b h1r,
    convert nat.zero_le _,
    rw [card_eq_zero, eq_empty_iff_forall_not_mem],
    intros A HA, apply h₁ A HA A HA, rw disjoint_self_iff_empty, 
    rw ← card_eq_zero, rw ← b, apply h₂ _ HA,
  by_contra size, replace size := lt_of_not_ge size,
  set 𝒜bar := 𝒜.image (λ A, univ \ A),
  have: disjoint 𝒜 (shadow^[n-2*r] 𝒜bar),
    rw disjoint_right, intros A hAbar hA, 
    simp [sub_iff_shadow_iter, mem_image] at hAbar,
    rcases hAbar with ⟨_, ⟨C, hC, rfl⟩, AsubnotC, _⟩, 
    apply h₁ A hA C hC (disjoint_of_subset_left AsubnotC sdiff_disjoint),
  have: r ≤ n := trans (le_of_lt h₃) (nat.div_le_self n 2), 
  have: 1 ≤ n := trans ‹1 ≤ r› ‹r ≤ n›,
  have z: 𝒜bar.card > nat.choose (n-1) (n-r),
    convert size using 1, rw card_image_of_inj_on, intros A _ B _ k, replace k := sdiff_partially_injective k,
      simp [ext] at k, rwa ext,
    apply choose_symm', rw [← nat.add_sub_assoc ‹r ≥ 1›, nat.sub_add_cancel ‹r ≤ n›],
  have: is_layer 𝒜bar (n - r),
    intro A, rw mem_image, rintro ⟨B, Bz, rfl⟩, rw card_univ_diff, rw card_fin, rw h₂ _ Bz, 
  have: n - 2 * r ≤ n - r, rw nat.sub_le_sub_left_iff, apply nat.le_mul_of_pos_left zero_lt_two, assumption,
  have kk := lovasz_form ‹n - 2 * r ≤ n - r› (by rwa nat.sub_le_sub_left_iff (trans h1r ‹r ≤ n›)) (nat.sub_le_self _ _) ‹is_layer 𝒜bar (n - r)› (le_of_lt z), 
  have q: n - r - (n - 2 * r) = r, rw nat.sub.right_comm, rw nat.sub_sub_self, rw two_mul, apply nat.add_sub_cancel,
  rw [mul_comm, ← nat.le_div_iff_mul_le' zero_lt_two], apply le_of_lt ‹_›, 
  rw q at kk, 
  have: nat.choose n r < card (𝒜 ∪ (shadow^[n - 2 * r] 𝒜bar)),
    rw card_disjoint_union ‹_›, 
    convert lt_of_le_of_lt (nat.add_le_add_left kk _) (nat.add_lt_add_right size _),
    convert nat.choose_succ_succ _ _, any_goals {rwa [nat.sub_one, nat.succ_pred_eq_of_pos]}, 
  apply not_le_of_lt this,
  convert size_in_layer _, rw card_fin,
  rw ← union_layer, refine ⟨‹_›, _⟩,
  intros B hB, rw sub_iff_shadow_iter at hB, 
  rcases hB with ⟨A, hA, _, cards⟩, rw [card_sdiff ‹B ⊆ A›, ‹is_layer 𝒜bar (n - r)› _ ‹A ∈ _›] at cards, 
  rw ← q, rw ← cards, rw nat.sub_sub_self, rw ← ‹is_layer 𝒜bar (n - r)› _ ‹A ∈ _›, apply card_le_of_subset ‹B ⊆ A›
end