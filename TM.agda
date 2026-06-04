{-# OPTIONS --without-K   --safe #-}

open import Data.Nat.Properties
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum

------- strings/State/Config ---------

data alphabet : Set where
  Alph : (Σ : ℕ) → (0 < Σ) → alphabet

in-alph : (a : ℕ) → (Σ : alphabet) → Set
in-alph a (Alph Σ 0<Σ) = a < Σ

data letter (Σ : alphabet) : Set where
  Lett : (a : ℕ) → (in-alph a Σ) → letter Σ


string : (Σ : alphabet) → Set
string Σ = List (letter Σ)

-- return an alphabet with one more letter
add-letter : (Σ : alphabet) → alphabet
add-letter (Alph Σ 0<Σ) = Alph (suc Σ) (s≤s z≤n)

-- return the new letter (the last one)
□-letter : {Σ : alphabet} → letter (add-letter Σ)
□-letter {Alph Σ 0<Σ} =  Lett Σ ≤-refl

state : (Q : alphabet) → Set
state Q = letter Q

data config (Σ : alphabet) (Q : alphabet) : Set where
  Conf : string Σ → letter Σ → string Σ → state Q → config Σ Q


data direction : Set where
  Left : direction
  Right : direction
  Down : direction

data final : Set where
  Final : final

TM-δ : {Σ : alphabet} → {Q : alphabet} →  Set
TM-δ {Σ} {Q} = letter (add-letter Σ) → state Q → final ⊎ letter (add-letter Σ) × state Q × direction


data TM (Σ : alphabet) (Q : alphabet) : Set where
  Tm :  (qi : state Q) → (δ : TM-δ {Σ} {Q}) → TM Σ Q

get-qi : {Σ Q : alphabet} → (tm : TM Σ Q) → state Q
get-qi (Tm qi _ ) = qi


get-δ : {Σ Q : alphabet} → (tm : TM Σ Q) → TM-δ {Σ} {Q}
get-δ (Tm _ δ ) = δ


lift-letter : ∀ {Σ} → (a : letter Σ) → letter  (add-letter Σ)
lift-letter {Alph Σ 0<Σ} (Lett a a<Σ) = Lett a (s≤s (<⇒≤ a<Σ))


-- require termination checking!
-- TM-config-list :{Σ Q : alphabet} → (tm : TM Σ Q) → List (config Σ Q)
-- TM-config-list {Σ} {Q} (Tm qi qf δ) = {!!}
--   where
--     TM-config-list-aux : config Σ Q → List (config Σ Q)
--     TM-config-list-aux (Tm qi qf δ) = {!!}

