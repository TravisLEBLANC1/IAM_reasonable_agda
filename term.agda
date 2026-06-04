{-# OPTIONS --without-K   --safe #-}

open import Data.Nat
open import Data.Fin using (Fin; zero; suc; _≟_; fromℕ)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat.Properties
open import Data.Nat.Binary.Properties using (x<y⇒suc[x]≤y)
open import Data.List.Properties using (++-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open import Agda.Builtin.Nat using (_-_)
open import Data.Sum
open import Data.Product


open import Utils-integers
open import TM

-- inspired by
-- https://bentnib.org/posts/2020-08-13-non-idempotent-intersection-types.html
data term : ℕ → Set where
  `_  : ∀ {n} → Fin n → term n
  ƛ   : ∀ {n} → term (suc n) → term n
  _·_ : ∀ {n} → term n → term n → term n

infixl 20 _·_
infix 40 `_

liftFin : ∀ {n m} → n ≤ m → Fin n → Fin m
liftFin z≤n ()
liftFin (s≤s le) zero    = zero
liftFin (s≤s le ) (suc x) = suc (liftFin le x)

-- capturing lift
lift' : ∀ {n m} → term n → n ≤ m → term m
lift' (` x)     le = ` liftFin le x
lift' (ƛ t)     le = ƛ (lift' t (s≤s le))
lift' (t₁ · t₂) le = lift' t₁ le · lift' t₂ le

-- capturing lift
lift : ∀ {m} → term zero → term m
lift t = lift' t z≤n


liftFinNC : ∀ {n m} → n ≤ m → Fin n → Fin m
liftFinNC z≤n ()
liftFinNC (s≤s z≤n) zero    = zero
liftFinNC (s≤s (s≤s le)) zero    = suc (liftFinNC (s≤s le) zero)
liftFinNC (s≤s le ) (suc x) = suc (liftFinNC le x)

-- non-capturing lift
liftNC' : ∀ {n m} → term n → n ≤ m → term m
liftNC' (` x)     le = ` liftFinNC le x
liftNC' (ƛ t)     le = ƛ (liftNC' t (s≤s le))
liftNC' (t₁ · t₂) le = liftNC' t₁ le · liftNC' t₂ le

-- non-capturing lift
liftNC : ∀ {m} → term zero → term m
liftNC t = liftNC' t z≤n


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




-- (ƛ ... ƛ. t) with N ƛs above t
-- but t can talk about variable outside of N
N-ƛ : (N : ℕ) → (N' : ℕ) → N ≥ N' →(t : term N) → term (N  -  N')
N-ƛ N zero le t = t
N-ƛ N (suc N') le  t = ƛ (subst (λ r → term r) (sym (suc--suc le)) (N-ƛ N N' (≥-suc le) t))
  where
    suc--suc : ∀ {N N' : ℕ} → N ≥ N' → suc (N - N') ≡ suc N - N'
    suc--suc z≤n = refl
    suc--suc (s≤s le) = suc--suc  le

-- (ƛ ... ƛ. t)
N-ƛ' : (N : ℕ) → (t : term N) → term zero
N-ƛ' N t  = subst (λ r → term r) (n∸n≡0 N ) (N-ƛ N N ≤-refl t)


-- N-· : {M : ℕ} → (N : ℕ) → (F : (n : ℕ) → term M) → term M
-- N-· zero F = F zero
-- N-· (suc N) F = F (suc N) · (N-· N F)

N-· : {M : ℕ} → (Σ : alphabet) → (F : (a : letter Σ)→ term M) → term M
N-· {M} (Alph Σ 0<Σ) F = N-·-aux Σ ≤-refl
  where
    N-·-aux : (N : ℕ) → N ≤ Σ  → term M
    N-·-aux zero le = F (Lett 0 0<Σ)
    N-·-aux (suc N) le = F (Lett N le) · (N-·-aux N (≥-suc le) )

-- ƛ ... ƛ. a
letter-term : {Σ : alphabet} → (a : letter Σ) → term zero
letter-term {Alph Σ 0<Σ}  (Lett a a<Σ)  = N-ƛ' Σ (lift' (` fromℕ a) a<Σ)

-- ƛ ... ƛ. q
state-term : {Q : alphabet} → (q : state Q) → term zero
state-term {Alph Q 0<Q}  (Lett q q<Q)  = N-ƛ' Q (lift' (` fromℕ q) q<Q)


-- ƛ ... ƛ.ƛε. ε
ε-term : (Σ : alphabet) → term zero
ε-term (Alph Σ 0<Σ) = N-ƛ' (suc(Σ)) (lift' (` fromℕ 0) (s≤s z≤n))

--  (ƛ ... ƛ.ƛε. a (... (ƛ ... ƛ.ƛε. ε))
string-term : {Σ : alphabet} → (s : string Σ) → term zero
string-term {Σ} [] = ε-term Σ
string-term {Alph Σ 0<Σ}  ((Lett a a<Σ) ∷ s) = N-ƛ' (suc(Σ)) (lift' (` fromℕ a) (s≤s (<⇒≤ a<Σ)) · (lift (string-term  s)))

⟨_,_,_,_⟩ : {M : ℕ} → term (suc M) → term (suc M) → term (suc M) → term (suc M) → term M
⟨_,_,_,_⟩ u a v q  = ƛ (` zero · u · a · v · q)

infix 30 ⟨_,_,_,_⟩


config-term : {Σ Q : alphabet} → config Σ Q → term zero
config-term {Σ} {Q} (Conf u a v q) =
            ⟨ (lift (string-term u)) , (lift (letter-term a)) , (lift (string-term v)) , (lift (state-term q)) ⟩
 
config-term-u : {Σ Q : alphabet} {M : ℕ} → term (suc M) → letter Σ → string Σ → state Q → term M
config-term-u {Σ} {Q} u a v q =
  ⟨ u , lift (letter-term a) , lift (string-term v) , lift (state-term q) ⟩

config-term-v : {Σ Q : alphabet} {M : ℕ} → string Σ → letter Σ → term (suc M)  → state Q → term M
config-term-v {Σ} {Q} u a v q =
  ⟨ lift (string-term u) , lift (letter-term a) , v , lift (state-term q) ⟩

config-term-uv : {Σ Q : alphabet} {M : ℕ} → term (suc M) → letter Σ → term (suc M)  → state Q → term M
config-term-uv {Σ} {Q} u a v q =
    ⟨ u , lift (letter-term a) , v , lift (state-term q) ⟩

config-term-uv' : {Σ Q : alphabet} {M : ℕ} → term  M → letter Σ → term M  → state Q → term M
config-term-uv' {Σ} {Q} {M}  u a v q =
   ⟨ liftNC' u (n≤1+n M) , lift (letter-term a) , liftNC' v (n≤1+n M) , lift (state-term q) ⟩


-- ƛk ƛs. k (a s)
append : (Σ : alphabet) → (a : letter Σ) → term zero
append (Alph Σ 0<Σ) (Lett a a<Σ) = ƛ (ƛ (` zero · as-term))
  where
    a-term : term (suc(suc(Σ)))
    a-term = lift' (` fromℕ a) (≤-step (≤-step a<Σ))

    s-term : term (suc(suc(Σ)))
    s-term = ` (fromℕ (suc(Σ)))

    as-term : term 2
    as-term rewrite sym (sucsuca--a Σ) = N-ƛ (suc (suc Σ)) Σ (≥-suc (≥-suc ≤-refl)) (a-term · s-term)


module TM-Module (Σ : alphabet) (Q : alphabet) (tm : TM Σ Q) where
  Σ□ = add-letter Σ
  qi = get-qi tm
  δ = get-δ tm

-- because it's easier to have the special case being 0, we assume that the letter 0 does not exists
-- 0 is kept for the case of ε

  --ƛx ƛk ƛs. s N N1 .. NΣ
  liftaux : term zero
  liftaux = ƛ (ƛ (ƛ (s · N-· Σ F)))
    where
      x = ` suc (suc zero)
      k = ` suc zero
      s = ` zero

      -- x (append_a k)
      liftN : (Σ : alphabet) → (a : letter Σ) → term 3
      liftN Σ a =  x · (lift (append Σ a) · k)

      F : (a : letter Σ) → term 3
      F (Lett 0 0<Σ) = k · lift (ε-term Σ□)       -- k ε
      F a = liftN Σ□ (lift-letter {Σ} a)            -- x (append_a k)

  lift-term :  term zero
  lift-term = omega · (liftaux)

  init-term :  term zero
  init-term = ƛ ((lift lift-term) · ƛ (` (suc zero) · config-term-v {Σ = Σ□} {Q = Q}  [] □-letter (` zero) qi))

  --ƛx ƛk ƛy. y (ƛu ƛa ƛv ƛq. q M0 M1 .. M(Q-1))
  transaux :  term zero
  transaux = ƛ (ƛ (ƛ (y · ƛ (ƛ (ƛ (ƛ (q · N-· Q FM)))))))
    where
      x = `  suc (suc (suc (suc (suc (suc zero)))))
      k = `  suc (suc (suc (suc (suc zero))))
      y = `  zero
      u = `  suc (suc (suc zero))
      a =  ` suc (suc zero)
      v =  ` suc zero
      q =  ` zero

      -- ƛu. append a (ƛw. x k ⟨  ⟩)
      FL :(a' : letter Σ□) → (q' : state Q) → (a : letter Σ□) → term 7
      FL a' q' (Lett 0 0<Σ□) = {!!}
      FL a' q' a = ƛ {!!}

      FR : (a' : letter Σ□) → (q' : state Q) → (a : letter Σ□) → term 7
      FR a' q' a = {!!}

      FN : (q : state Q) → (a : letter Σ□) → term 7
      FN q a with δ  a q
      ... | inj₁ Final = k · config-term-uv' u a v q
      ... | inj₂ (a' , q' , Left)   = x · k · config-term-uv' u a' v q'
      ... | inj₂ (a' , q' , Rigt) =  u · (N-· Σ□ (FL a' q'))
      ... | inj₂ (a' , q' , Down)   = v · (N-· Σ□ (FR a' q'))

      FM : (q : state Q) → term 7
      FM q = a · N-· Σ□ (FN q)

  trans-term :  term zero
  trans-term = omega · (transaux)
