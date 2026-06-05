{-# OPTIONS --without-K  --safe #-}

-- {-# OPTIONS --allow-unsolved-metas #-}

--/!\ this file is almost entirely LLMs proofs


open import Data.Nat
open import Data.Nat.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open import Agda.Builtin.Nat using (_-_)
open import Data.Sum using (_⊎_)


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
m*suc≥1 (s≤s le) = s≤s z≤n

2*m≥1 : {m : ℕ} → m ≥ 1 → 2 * m ≥ 1
2*m≥1 {m} le = ≤-trans le (m≤m+n m (m + zero))


suc-pred≥1 : (n : ℕ) → n ≥ 1 → n ≡ suc (pred n)
suc-pred≥1 n (s≤s  le) = refl

suc-pred-pow : (n : ℕ) → pow-minus1 (suc n) ≡ suc (pred (pow-minus1 (suc n)))
suc-pred-pow n = suc-pred≥1 (pow-minus1 (suc n)) (pow-≥1 {suc n})

pow-≥2 : ∀ {n : ℕ} → pow-minus1 (suc n) ≥ 2
pow-≥2 {zero} = s≤s (s≤s (z≤n))
pow-≥2 {suc n} =
  subst (2 ≤_) (sym (+-comm (2 ^ (suc (suc n))) (pow-minus1 (suc n))))
    (≤-trans (pow-≥2 {n}) (m≤m+n (pow-minus1 (suc n)) (2 ^ (suc (suc n)))))

pow-sucsuc : ∀ {n : ℕ} →  2 * (2 ^ n) ≤ pow-minus1 (suc (suc n))
pow-sucsuc {n} =
  subst (2 * (2 ^ n) ≤_) (sym (+-assoc (2 ^ (suc n)) (2 ^ (suc n) + 0) (pow-minus1 (suc n)))) 
    (m≤m+n (2 ^ (suc n)) ((2 ^ (suc n) + 0) + pow-minus1 (suc n)))

pow-factor : {m n : ℕ} → m * (pow-minus1 (suc n)) ≡ m + m * pred (pow-minus1 (suc n))
pow-factor {m} {n} = 
  begin
    m * pow-minus1 (suc n)                             ≡⟨ cong (m *_) (suc-pred-pow n) ⟩
    m * suc (pred (pow-minus1 (suc n))) ≡⟨ *-suc m (pred (pow-minus1 (suc n))) ⟩
    m + m * pred (pow-minus1 (suc n)) ∎

pow-factor2 : {n : ℕ} → pred (pow-minus1 (suc n))  ≡ 2 * pow-minus1 n
pow-factor2 {zero} = refl
pow-factor2 {suc n} = 
  let A = 2 ^ (suc n)
      B = pow-minus1 n
      two-times : ∀ X → 2 * X ≡ X + X
      two-times X = cong (X +_) (+-identityʳ X)

      rearrange : ∀ X Y → (X + X) + (Y + Y) ≡ (X + Y) + (X + Y)
      rearrange X Y = 
        begin
          (X + X) + (Y + Y)
        ≡⟨ +-assoc X X (Y + Y) ⟩
          X + (X + (Y + Y))
        ≡⟨ cong (X +_) (sym (+-assoc X Y Y)) ⟩
          X + ((X + Y) + Y)
        ≡⟨ cong (λ z → X + (z + Y)) (+-comm X Y) ⟩
          X + ((Y + X) + Y)
        ≡⟨ cong (X +_) (+-assoc Y X Y) ⟩
          X + (Y + (X + Y))
        ≡⟨ sym (+-assoc X Y (X + Y)) ⟩
          (X + Y) + (X + Y)
        ∎
  in
  begin
    pred (pow-minus1 (suc (suc n))) 
  ≡⟨⟩
    pred (2 ^ (suc (suc n)) + pow-minus1 (suc n))
  ≡⟨ cong (λ x → pred (2 ^ (suc (suc n)) + x)) (suc-pred-pow n) ⟩
    pred (2 ^ (suc (suc n)) + suc (pred (pow-minus1 (suc n))))
  ≡⟨ cong pred (+-suc (2 ^ (suc (suc n))) (pred (pow-minus1 (suc n)))) ⟩
    pred (suc (2 ^ (suc (suc n)) + pred (pow-minus1 (suc n))))
  ≡⟨⟩
    2 ^ (suc (suc n)) + pred (pow-minus1 (suc n))
  ≡⟨ cong (_+ pred (pow-minus1 (suc n))) (two-times A) ⟩
    (A + A) + pred (pow-minus1 (suc n))
  ≡⟨ cong ((A + A) +_) (pow-factor2 {n}) ⟩
    (A + A) + (2 * B)
  ≡⟨ cong ((A + A) +_) (two-times B) ⟩
    (A + A) + (B + B)
  ≡⟨ rearrange A B ⟩
    (A + B) + (A + B)
  ≡⟨ sym (two-times (A + B)) ⟩
    2 * (A + B)
  ≡⟨⟩
    2 * pow-minus1 (suc n)
  ∎

pow-factor2m : {n m : ℕ} → m * pred (pow-minus1 (suc n))  ≡ (2 * m) * pow-minus1 n
pow-factor2m {n} {m} =
  begin
    m * pred (pow-minus1 (suc n))
  ≡⟨ cong (m *_) (pow-factor2 {n}) ⟩
    m * (2 * pow-minus1 n)
  ≡⟨ sym (*-assoc m 2 (pow-minus1 n)) ⟩
    (m * 2) * pow-minus1 n
  ≡⟨ cong (_* pow-minus1 n) (*-comm m 2) ⟩
    (2 * m) * pow-minus1 n
  ∎

pred≥1 : {k : ℕ} → k ≥ 2 → pred k ≥ 1
pred≥1 {k} (s≤s (s≤s le)) = s≤s z≤n

x≤suc[x] : (x : ℕ) → (x ≤ suc x)
x≤suc[x] zero = z≤n
x≤suc[x] (suc x) = s≤s (x≤suc[x] x)


≥-suc : ∀ {N N' : ℕ} → N ≥ suc N' → N ≥ N'
≥-suc (s≤s {n = n} le) = ≤-trans le (n≤1+n n)

sucsuca--a : ∀ (a : ℕ) → suc (suc a) ∸ a ≡ 2
sucsuca--a zero = refl
sucsuca--a (suc a) = sucsuca--a a
