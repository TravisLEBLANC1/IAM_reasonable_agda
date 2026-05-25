{-# OPTIONS --without-K  #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _≤_; _≥_;  z≤n; s≤s; pred)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-identityˡ ; *-identityˡ;  *-identityʳ; *-zeroˡ ;*-zeroʳ; suc-injective; +-suc; *-suc; *-monoʳ-≤; ≤-trans; m≤m+n; +-monoʳ-≤; *-comm; *-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

------ Integer manipulations -------
-- pow-minus1 n = 2^{n+1} - 1
pow-minus1 : (n : ℕ) → ℕ
pow-minus1 zero = suc (zero)
pow-minus1 (suc n) = 2 ^(suc n) + pow-minus1 n

pow-≥1 : ∀ {n : ℕ} → pow-minus1 n ≥ 1
pow-≥1 {zero} = s≤s z≤n
pow-≥1 {suc n} = lemaux  (pow-≥1 {n})
  where
    lemaux : ∀ {k} → 1 ≤ pow-minus1 n → 1 ≤ k + pow-minus1 n
    lemaux {zero}  h = h
    lemaux {suc k} h = s≤s z≤n

2^n≥1 : {n : ℕ} → 2 ^ n ≥ 1
2^n≥1 {0} = s≤s z≤n
2^n≥1 {suc n} = ≤-trans (2^n≥1 {n}) (m≤m+n (2 ^ n) (2 ^ n + 0))

m*suc≥1 : {m k : ℕ} → m ≥ 1 → m * (suc k) ≥ 1
m*suc≥1 = {!!}

2*m≥1 : {m : ℕ} → m ≥ 1 → 2 * m ≥ 1
2*m≥1 {m} le = ≤-trans le (m≤m+n m (m + zero))

pow-≥2 : ∀ {n : ℕ} → pow-minus1 (suc n) ≥ 2
pow-≥2 {zero} = s≤s (s≤s (z≤n))
pow-≥2 {suc n} = {!!}

pow-sucsuc : ∀ {n : ℕ} →  2 * (2 ^ n) ≤ pow-minus1 (suc (suc n))
pow-sucsuc = {!!}

pow-factor : {m n : ℕ} → m * (pow-minus1 (suc n)) ≡ m + m * pred (pow-minus1 (suc n))
pow-factor = {!!}

pow-factor2 : {n : ℕ} → pred (pow-minus1 (suc n))  ≡ 2 * pow-minus1 n
pow-factor2 = {!!}

pow-factor2m : {n m : ℕ} → m * pred (pow-minus1 (suc n))  ≡ (2 * m) * pow-minus1 n
pow-factor2m = {!!}

pred≥1 : {k : ℕ} → k ≥ 2 → pred k ≥ 1
pred≥1 {k} (s≤s (s≤s le)) = s≤s z≤n
