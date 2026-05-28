{-# OPTIONS --without-K  --safe  #-}

open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _≤_; _<_; _≥_;  z≤n; s≤s; pred)
open import Data.Fin using (Fin; zero; suc; _≟_; fromℕ)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat.Properties using (n∸n≡0;≤-refl)
open import Data.List.Properties using (++-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open import Agda.Builtin.Nat using (_-_)

open import Utils-integers

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


------- strings ---------

data alphabet : Set where
  Alph : (Σ : ℕ) → (0 < Σ) → alphabet

in-alph : (a : ℕ) → (Σ : alphabet) → Set
in-alph a (Alph Σ 0<Σ) = a < Σ

data letter (Σ : alphabet) : Set where
  Lett : (a : ℕ) → (in-alph a Σ) → letter Σ

-- a string is a list of letter,
-- a letter is an integer a < Σ, where Σ is the size of the alphabet
data string (Σ : alphabet) : Set where
  Eps : string Σ
  Cons : letter Σ → string Σ → string Σ


-- (ƛ ... ƛ. t)
N-ƛ : (N : ℕ) → (t : term N) → term zero
N-ƛ N t  = subst (λ r → term r) (n∸n≡0 N ) (N-ƛ-aux N N ≤-refl t)
  where
    N-ƛ-aux : (N : ℕ) → (N' : ℕ) → N ≥ N' →(t : term N) → term (N  -  N')
    N-ƛ-aux N zero le t = t
    N-ƛ-aux N (suc N') le  t = ƛ (subst (λ r → term r) (sym (suc--suc le)) (N-ƛ-aux N N' (≥-suc le) t))

-- ƛ ... ƛ. a
letter-term : (Σ : alphabet) → (a : letter Σ) → term zero
letter-term (Alph Σ 0<Σ)  (Lett a a<Σ)  = N-ƛ Σ (lift' (` fromℕ a) a<Σ)

ε-letter : (Σ : alphabet) → letter Σ
ε-letter (Alph Σ 0<Σ)  = Lett 0 0<Σ

-- ƛ ... ƛ. ε
ε-term : (Σ : alphabet) → term zero
ε-term Σ = letter-term Σ (ε-letter Σ)

--  (ƛ ... ƛ. a (... (ƛ ... ƛ. ε))
string-term : (Σ : alphabet) → (s : string Σ) → term zero
string-term Σ Eps = ε-term Σ
string-term (Alph Σ 0<Σ)  (Cons (Lett a a<Σ) s) = N-ƛ Σ (lift' (` fromℕ a) a<Σ · (lift (string-term (Alph Σ 0<Σ) s)))

-- append : (Σ : alphabet) → (a : letter Σ) → term zero
-- append Σ a = ƛ (ƛ (` zero · {!N-ƛ !}))
