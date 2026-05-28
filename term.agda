{-# OPTIONS --without-K  --safe  #-}

open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _≤_; _≥_;  z≤n; s≤s; pred)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)

-- inspired by
-- https://bentnib.org/posts/2020-08-13-non-idempotent-intersection-types.html
data term : ℕ → Set where
  `_  : ∀ {n} → Fin n → term n
  ƛ   : ∀ {n} → term (suc n) → term n
  _·_ : ∀ {n} → term n → term n → term n

liftFin : ∀ {n m} → n ≤ m → Fin n → Fin m
liftFin z≤n ()
liftFin (s≤s le) zero    = zero
liftFin (s≤s le ) (suc x) = suc (liftFin le x)

lift' : ∀ {n m} → term n → n ≤ m → term m
lift' (` x)     le = ` liftFin le x
lift' (ƛ t)     le = ƛ (lift' t (s≤s le))
lift' (t₁ · t₂) le = lift' t₁ le · lift' t₂ le

lift : ∀ {m} → term zero → term m
lift t = lift' t z≤n

infixl 20 _·_
infix 40 `_


data type : Set where
  ⋆    : type
  _↦_ : List type → type → type

infixr 30 _↦_


data ctx : ℕ → Set where
  nil : ctx zero
  _,-_ : ∀ {n} → ctx n → List type → ctx (suc n)

empty : ∀{n} → ctx n
empty {zero}  = nil
empty {suc n} = empty {n} ,- []

_+++_ : ∀{n} → ctx n → ctx n → ctx n
nil        +++ nil       = nil
(Γ₁ ,- σ₁) +++ (Γ₂ ,- σ₂) = (Γ₁ +++ Γ₂) ,- (σ₁ ++ σ₂)

+++empty : ∀ {n} {Γ : ctx n} → (Γ +++ empty) ≡ Γ
+++empty {zero} {nil} = refl
+++empty {suc n} {Γ ,- σ} = cong₂ _,-_ +++empty (++-identityʳ σ )


liftctx : ∀ {n m} → n ≤ m  → ctx n → ctx m
liftctx z≤n nil         = empty
liftctx (s≤s le) (Γ ,- x) = liftctx le Γ ,- x

liftctxempty : ∀ {n m} →(le : n ≤ m)  → liftctx le (empty {n}) ≡ empty {m}
liftctxempty z≤n = refl
liftctxempty (s≤s le) = subst (λ r → (r ,- []) ≡ (empty ,- [])) (sym (liftctxempty le)) refl


---------- Terms  -------

church-aux : ℕ → term (suc (suc zero))
church-aux zero = ` zero
church-aux (suc n) = ` (suc zero) · church-aux n

-- λfx.f (f .. (f x))
church : ℕ → term zero
church n = ƛ (ƛ (church-aux n))

-- λfx.f x
one : term zero
one = ƛ (ƛ (` (suc zero) · ` zero))

-- λnfx.n f (n f x)
double : term zero
double = ƛ (ƛ (ƛ (` (suc (suc zero)) · ` (suc zero) · (` (suc (suc zero)) · ` (suc zero) · ` zero))))

-- λxny.n y (x x (n + n) y)
theta : term zero
theta = ƛ (ƛ (ƛ (` (suc zero) · ` zero · (` (suc (suc zero)) · ` (suc (suc zero)) · ((lift double) ·  (` (suc zero))) · ` zero))))

-- The inlining fixpoint
omega : term zero
omega = theta · theta · one

