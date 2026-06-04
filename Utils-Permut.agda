{-# OPTIONS --without-K --safe  #-}

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import term

module Utils-Permut {X : Set} where
  data _⋈_ : List X -> List X -> Set where
    nil     : [] ⋈ []
    skip    : ∀ {x l₁ l₂}  -> l₁ ⋈ l₂ -> (x ∷ l₁) ⋈ (x ∷ l₂)
    swap    : ∀ {x y l}    ->           (x ∷ y ∷ l) ⋈ (y ∷ x ∷ l)
    ⋈-trans : ∀ {l₁ l₂ l₃} -> l₁ ⋈ l₂ -> l₂ ⋈ l₃ -> l₁ ⋈ l₃

  ⋈-refl : ∀ {l} -> l ⋈ l
  ⋈-refl {[]}    = nil
  ⋈-refl {x ∷ l} = skip ⋈-refl

  infixr 2 _⋈⟨_⟩_
  infix  3 _■


  _⋈⟨_⟩_ : ∀ (l₁ : List X) {l₂ l₃ : List X} → l₁ ⋈ l₂ → l₂ ⋈ l₃ → l₁ ⋈ l₃
  _ ⋈⟨ p₁₂ ⟩ p₂₃ = ⋈-trans p₁₂ p₂₃

  _■ : ∀ (l : List X) → l ⋈ l
  _■ l = ⋈-refl

  ⋈-trans2 : ∀ {l₁ l₂ l₃ l₄ }  →  l₁ ⋈ l₂ → l₂ ⋈ l₃ → l₃ ⋈ l₄ →  l₁  ⋈ l₄
  ⋈-trans2 {l₁} { l₂} { l₃} { l₄ }  p1 p2 p3 =
                l₁ ⋈⟨ p1 ⟩
                l₂ ⋈⟨ p2 ⟩
                l₃ ⋈⟨ p3 ⟩
                l₄ ■

  ⋈-transwapr : ∀ {l' l x y} →  l' ⋈ (x ∷ y ∷ l)  → l' ⋈ (y ∷ x ∷ l)
  ⋈-transwapr r = ⋈-trans r swap

  ⋈-rotate : ∀ {l₁ l₂ x } → (l₁ ++ (x ∷ l₂)) ⋈  (x  ∷ (l₁ ++  l₂))
  ⋈-rotate {[]} = ⋈-refl
  ⋈-rotate {y ∷ l₁} = ⋈-trans (skip ⋈-rotate) swap

  ⋈-sym : ∀ {l₁ l₂} → l₁ ⋈  l₂ → l₂ ⋈ l₁
  ⋈-sym nil = nil
  ⋈-sym (skip p) = skip (⋈-sym p)
  ⋈-sym (swap) = swap
  ⋈-sym (⋈-trans p₁ p₂) = ⋈-trans (⋈-sym p₂)  (⋈-sym p₁)

  ⋈-comm : ∀ l₁ l₂ → (l₁ ++ l₂) ⋈ (l₂ ++ l₁)
  ⋈-comm [] l₂ rewrite ++-identityʳ l₂ =  ⋈-refl
  ⋈-comm (x ∷ l₁) l₂ = ⋈-trans (skip (⋈-comm l₁ l₂)) (⋈-sym ⋈-rotate)

  ⋈-skip≡ : ∀ {x y l₁ l₂}   → x ≡ y  → l₁ ⋈ l₂ → (x ∷ l₁) ⋈ (y ∷ l₂)
  ⋈-skip≡ {x} {y}  {l₁} {l₂} p h = subst (λ r → (x ∷ l₁) ⋈ (r ∷ l₂)) p (skip h)

  ⋈-cong++ : ∀ {l₁ l₂ l₃} → l₂ ⋈ l₃ → (l₁ ++ l₂ )  ⋈  (l₁ ++ l₃ )
  ⋈-cong++ {[]} p = p
  ⋈-cong++ {x ∷ l₁} p = skip (⋈-cong++ p)

  ⋈-≡ : ∀ {l₁ l₂ } → l₁ ≡ l₂ → l₁ ⋈ l₂
  ⋈-≡ refl = ⋈-refl

  skip-≡ : ∀ {x y l₁ l₂ } → x ≡ y → l₁ ⋈  l₂ → (x ∷ l₁) ⋈ (y ∷ l₂)
  skip-≡ refl H = skip H

  ⋈++[] : ∀ {σ} → (σ ++ []) ⋈ σ
  ⋈++[] {σ} rewrite ++-identityʳ σ = ⋈-refl

  ⋈-[] : ∀ {σ} → σ ⋈ [] → σ ≡ []
  ⋈-[] {σ} nil = refl
  ⋈-[] {σ} (⋈-trans p₁ p₂) with ⋈-[] p₂
  ... | refl = ⋈-[] p₁

  ⋈-[A] : ∀ {A σ} → σ ⋈ [ A ] → σ ≡ [ A ]
  ⋈-[A] (skip p) with ⋈-[] p
  ... | refl = refl
  ⋈-[A] (⋈-trans p₁ p₂) with  ⋈-[A] p₂
  ... | refl = ⋈-[A] p₁
