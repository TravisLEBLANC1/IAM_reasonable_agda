{-# OPTIONS --without-K  --safe #-}

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _≤_; _≥_;  z≤n; s≤s; pred)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-identityˡ ; *-identityˡ;  *-identityʳ; *-zeroˡ ;*-zeroʳ; suc-injective; +-suc; *-suc; *-monoʳ-≤; ≤-trans; m≤m+n; +-monoʳ-≤; *-comm; *-assoc)
open import Axiom.Extensionality.Propositional using (Extensionality ; ExtensionalityImplicit )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open Eq.≡-Reasoning

open import Utils-Permut
open import term

-- todo: remove ext (not really needed I think)
-- postulate
--   ext : Extensionality (Agda.Primitive.lzero) (Agda.Primitive.lzero)


applyUpTo : {A : Set} →  (ℕ → A) → ℕ → List A
applyUpTo f zero    = []
applyUpTo f (suc n) = f n ∷ applyUpTo f n


apply-addlast : ∀ {B} {f : ℕ → B} (m : ℕ) → (f m ∷ applyUpTo f m) ⋈ (applyUpTo f (suc m))
apply-addlast m = ⋈-refl

apply-removelast : ∀ {B} {f : ℕ → B} (m : ℕ)→ m ≥ 1 → (applyUpTo f m) ⋈ (f (pred m) ∷ applyUpTo f (pred m))
apply-removelast m (s≤s le) = ⋈-refl

apply-split+ : ∀ {B} {f : ℕ → B} (m : ℕ) (m' : ℕ) → applyUpTo f (m + m') ⋈ (applyUpTo f m ++ applyUpTo (λ i → f (i + m)) m')
apply-split+ {f = f} m 0  rewrite +-identityʳ m |  ++-identityʳ (applyUpTo f m) = ⋈-refl
apply-split+ {f = f} m (suc m') rewrite +-suc m m' = ⋈-sym (
             (applyUpTo f m ++ f (m' + m) ∷ applyUpTo (λ i → f (i + m)) m') ⋈⟨ ⋈-rotate ⟩
              f (m' + m) ∷ (applyUpTo f m ++  applyUpTo (λ i → f (i + m)) m') ⋈⟨ ⋈-≡ (cong (λ r → f (r) ∷ (applyUpTo f m ++  applyUpTo (λ i → f (i + m)) m') ) (+-comm m' m) )  ⟩
              f (m + m') ∷ (applyUpTo f m ++  applyUpTo (λ i → f (i + m)) m') ⋈⟨ skip (⋈-sym (apply-split+ m m')) ⟩
              f (m + m') ∷ applyUpTo f (m + m') ■ )

apply-split+' : ∀ {B} {f : ℕ → B} (m : ℕ) (m' : ℕ) → (applyUpTo (λ i → f (i + m)) m' ++  applyUpTo f m ) ⋈  applyUpTo f (m + m')
apply-split+' {f = f} m n = ⋈-sym (⋈-trans (apply-split+ m n) (⋈-comm (applyUpTo f m) (applyUpTo (λ z → f (z + m)) n)))


apply-split+'' : ∀ {B} {f : ℕ → B} (a b : ℕ) →
              applyUpTo f (a + b) ≡ applyUpTo (λ i → f (i + b)) a ++ applyUpTo f b
apply-split+'' zero b    = refl
apply-split+'' {f = f} (suc a) b = cong (f (a + b) ∷_) (apply-split+'' a b)

apply-split-pred : ∀ {B} {f : ℕ → B} (m : ℕ) (k : ℕ)→ k ≥ 1 → (applyUpTo (λ i → f (i + m * (pred k))) m ++ applyUpTo f (m * pred k)) ⋈ applyUpTo f (m * k)
apply-split-pred {f = f} m (suc k') (s≤s le) rewrite *-suc m k' | +-comm m (m * k') =
    applyUpTo (λ i → f (i + m * k')) m ++ applyUpTo f (m * k')   ⋈⟨ ⋈-comm (applyUpTo (λ i → f (i + m * k')) m) (applyUpTo f (m * k')) ⟩
    applyUpTo f (m * k') ++ applyUpTo (λ i → f (i + m * k')) m   ⋈⟨ ⋈-sym (apply-split+ (m * k') m) ⟩
    applyUpTo f (m * k' + m) ■


apply-cong : ∀ {A : Set} {f g : ℕ → A} (n : ℕ) →
                 (∀ i → f i ≡ g i) → applyUpTo f n ≡ applyUpTo g n
apply-cong zero eq    = refl
apply-cong (suc n) eq = cong₂ _∷_ (eq n) (apply-cong n eq)

-- apply-exchange : ∀ {B} {f : ℕ → B} (m : ℕ) → (f m ∷ applyUpTo f m) ⋈ (f 0 ∷ applyUpTo (λ i → f (suc i)) m)
-- apply-exchange m = ⋈-trans (apply-addlast m) ⋈-refl

-- applyUpTo-ext : {A : Set} (f g : ℕ → A) (n : ℕ)
--               → (∀ i → f i ≡ g i)
--               → applyUpTo f n ≡ applyUpTo g n
-- applyUpTo-ext f g zero eq = refl
-- applyUpTo-ext f g (suc n) eq rewrite eq n | applyUpTo-ext f g n eq = refl


