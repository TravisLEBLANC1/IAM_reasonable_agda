{-# OPTIONS --without-K  #-}
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _≤_; _≥_;  z≤n; s≤s; pred)
open import Data.List using (List; []; _∷_; _++_; [_])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)

open import term
open import Utils-List
open import Utils-Permut


data _⋈ctx_ : ∀ {n} → ctx n → ctx n → Set where
  nil : nil ⋈ctx nil
  _,-_ : ∀ {n}{Γ₁ Γ₂ : ctx n}{σ₁ σ₂} → Γ₁ ⋈ctx Γ₂ → σ₁ ⋈ σ₂ → (Γ₁ ,- σ₁) ⋈ctx (Γ₂ ,- σ₂)

⋈ctx-refl : ∀ {n}{Γ : ctx n} → Γ ⋈ctx Γ
⋈ctx-refl {Γ = nil}    = nil
⋈ctx-refl {Γ = Γ ,- σ} = ⋈ctx-refl ,- ⋈-refl

⋈ctx-refl-empty : ∀ {n}{Γ : ctx n} → (Γ +++ empty)  ⋈ctx Γ
⋈ctx-refl-empty {n} {Γ} = subst (λ x → x ⋈ctx Γ) (sym +++empty) ⋈ctx-refl

⋈ctx-trans : ∀ {n} {Γ₁ Γ₂ Γ₃ : ctx n} → Γ₁ ⋈ctx Γ₂ → Γ₂ ⋈ctx Γ₃ → Γ₁ ⋈ctx Γ₃
⋈ctx-trans nil nil = nil
⋈ctx-trans (p1 ,- x1) (p2 ,- x2) = ⋈ctx-trans p1 p2 ,- ⋈-trans x1 x2

⋈ctx-empty : ∀ {n} {Γ : ctx n} → empty {n} ⋈ctx Γ → Γ ≡ empty
⋈ctx-empty nil = refl
⋈ctx-empty (p ,- x) with ⋈ctx-empty p | ⋈-[] (⋈-sym x)
... | refl | refl = refl

data _⊢v_⦂_ : ∀ {n} → ctx n → Fin n → type → Set where
  zero : ∀ {n τ} → (empty {n} ,- [ τ ]) ⊢v zero ⦂ τ
  suc  : ∀ {n τ i}{Γ : ctx n} → Γ ⊢v i ⦂ τ → (Γ ,- []) ⊢v (suc i) ⦂ τ

mutual
  data _⊢_⦂_ : ∀ {n} → ctx n → term n → type → Set where
    var : ∀ {n τ i}{Γ : ctx n} →
          Γ ⊢v i ⦂ τ →
          Γ ⊢ ` i ⦂ τ
    lam : ∀ {n σ τ t}{Γ : ctx n} →
          (Γ ,- σ) ⊢ t ⦂ τ →
          Γ ⊢ ƛ t ⦂ (σ ↦ τ)
    app : ∀ {n σ τ s t}{Γ Γ₁ Γ₂ : ctx n} →
          Γ₁ ⊢ s ⦂ (σ ↦ τ) →
          Γ₂ ⊢ t ⦂' σ →
          (Γ₁ +++ Γ₂) ⋈ctx Γ →
          Γ ⊢ (s · t) ⦂ τ
    lam⋆ : ∀ {n t} →
          empty {n} ⊢ ƛ t ⦂ ⋆

  data _⊢_⦂'_ : ∀ {n} → ctx n → term n → List type → Set where
    nil : ∀ {n}{t : term n} →
          empty ⊢ t ⦂' []
    _,~_∷_ : ∀ {n t σ τ}{Γ₁ Γ₂ Γ : ctx n} →
          Γ₁ ⊢ t ⦂ τ →
          (Γ₁ +++ Γ₂) ⋈ctx Γ →
          Γ₂ ⊢ t ⦂' σ →
          Γ ⊢ t ⦂' (τ ∷ σ)


singl⊢  : ∀ {n}  {Γ : ctx n}  {t A} →  Γ ⊢ t ⦂ A →  Γ  ⊢ t ⦂' [ A ]
singl⊢ p = p ,~ ⋈ctx-refl-empty ∷ nil

lift⊢v : ∀ {n m} {Γ : ctx n} {i : Fin n} {τ : type}
       → (le : n ≤ m) → Γ ⊢v i ⦂ τ → liftctx le Γ ⊢v liftFin le i ⦂ τ
lift⊢v (s≤s le) zero   rewrite liftctxempty le = zero
lift⊢v (s≤s le) (suc h) = suc (lift⊢v le h)

lift⋈ctx : ∀ {n m} {Γ₁ Γ₂ Γ : ctx n}
         → (le : n ≤ m) → (Γ₁ +++ Γ₂) ⋈ctx Γ → (liftctx le Γ₁ +++ liftctx le Γ₂) ⋈ctx liftctx le Γ
lift⋈ctx {n} {m} {Γ₁ = nil} {Γ₂ = nil} z≤n nil       rewrite +++empty {Γ = empty {m}} = ⋈ctx-refl
lift⋈ctx {n} {m} {Γ₁ = (Γ₃ ,- σ₁)} {Γ₂ = (Γ₄ ,- σ₂)} (s≤s le)  (p ,- x) = lift⋈ctx le p ,- x


mutual
  lift⊢' : ∀ {n m} {Γ : ctx n} {t : term n} {A : type}
         → (le : n ≤ m) → Γ ⊢ t ⦂ A → liftctx le Γ ⊢ lift' t le ⦂ A
  lift⊢' le (var h)       = var (lift⊢v le h)
  lift⊢' le (lam h)       = lam (lift⊢' (s≤s le) h)
  lift⊢' le (app h1 h2 h3) = app (lift⊢' le h1) (lift⊢'' le h2) (lift⋈ctx le h3)
  lift⊢' le lam⋆          rewrite liftctxempty le = lam⋆

  lift⊢'' : ∀ {n m} {Γ : ctx n} {t : term n} {As : List type}
          → (le : n ≤ m) → Γ ⊢ t ⦂' As → liftctx le Γ ⊢ lift' t le ⦂' As
  lift⊢'' le nil          rewrite liftctxempty le = nil
  lift⊢'' le (h1 ,~ h2 ∷ h3) = lift⊢' le h1 ,~ lift⋈ctx le h2 ∷ lift⊢'' le h3


lift⊢ : ∀ {A} → {n : ℕ} → {t : term zero} → nil ⊢ t ⦂ A → empty {n} ⊢ lift {n} t ⦂ A
lift⊢ H = lift⊢' z≤n H

mutual
  ⊢⋈ctx : ∀ {n}  {Γ₁ Γ₂ : ctx n}  {t A} →  Γ₁  ⊢ t ⦂ A →  Γ₁ ⋈ctx Γ₂ →  Γ₂   ⊢ t ⦂  A
  ⊢⋈ctx (var zero) (p ,- x) with ⋈ctx-empty p | ⋈-[A] (⋈-sym x)
  ... | refl | refl = var zero
  ⊢⋈ctx (var (suc m)) (p ,- x) with ⊢⋈ctx (var m) p | ⋈-[] (⋈-sym x)
  ... | var h | refl = var (suc h)
  ⊢⋈ctx (lam h) p = lam (⊢⋈ctx h (p ,- ⋈-refl))
  ⊢⋈ctx (app h1 h2 h3) p = app h1 h2 (⋈ctx-trans h3 p)
  ⊢⋈ctx lam⋆ p with ⋈ctx-empty p
  ... | refl = lam⋆

  ⊢⋈ctx' : ∀ {n} {Γ₁ Γ₂ : ctx n} {t As} → Γ₁ ⊢ t ⦂' As → Γ₁ ⋈ctx Γ₂ → Γ₂ ⊢ t ⦂' As
  ⊢⋈ctx' nil p with ⋈ctx-empty p
  ... | refl = nil
  ⊢⋈ctx' (h1 ,~ h2 ∷ h3) p = h1 ,~ ⋈ctx-trans h2 p ∷ h3

--  We could generalize this to any lifting of integer,
--  for the moment it's specialized for convenience
var0⊢⦂' : ∀ {σ} →  (nil ,- σ)  ⊢ ` zero ⦂' σ
var0⊢⦂' {[]} = nil
var0⊢⦂' {τ ∷ σ} = var zero ,~ ⋈ctx-refl ∷ var0⊢⦂'

var1⊢⦂' : ∀ {σ} →  (((nil ,- [] ) ,- σ) ,- [] )  ⊢ ` (suc zero) ⦂' σ
var1⊢⦂' {[]} = nil
var1⊢⦂' {τ ∷ σ} = var (suc zero) ,~ ⋈ctx-refl ∷ var1⊢⦂'

var2⊢⦂' : ∀ {σ} →  (((nil ,- []) ,- []) ,-  σ)  ⊢ ` zero ⦂' σ
var2⊢⦂' {[]} = nil
var2⊢⦂' {τ ∷ σ} = var zero ,~ ⋈ctx-refl ∷ var2⊢⦂'

var3⊢⦂' : ∀ {σ} →  (((nil ,- σ) ,- []) ,-  [])  ⊢ ` suc (suc zero) ⦂' σ
var3⊢⦂' {[]} = nil
var3⊢⦂' {τ ∷ σ} = var (suc (suc zero)) ,~ ⋈ctx-refl ∷ var3⊢⦂'

zero⦂≡ : ∀ {τ₁ τ₂} →  τ₁ ≡ τ₂ → (nil ,- [ τ₁ ] ) ⊢v   zero  ⦂  τ₂
zero⦂≡ refl = zero

zero2⦂≡ : ∀ {τ₁ τ₂} →  τ₁ ≡ τ₂ → ((nil ,- []) ,- [ τ₁ ] ) ⊢v   zero  ⦂  τ₂
zero2⦂≡ refl = zero



-- some alternative version of app
app₁ : ∀ {n Γ₁ Γ₂ τ₁ τ₂}{s t : term n} →
      Γ₁ ⊢ s ⦂ [ τ₁ ] ↦ τ₂ →
      Γ₂ ⊢ t ⦂ τ₁ →
      (Γ₁ +++ (Γ₂ +++ empty)) ⊢ s · t ⦂ τ₂
app₁ s-ok t-ok = app s-ok (t-ok ,~ ⋈ctx-refl ∷ nil) ⋈ctx-refl

app₂ : ∀ {n Γ₁ Γ₂ Γ₃  τ₁ τ₂ τ₃}{s t : term n} →
      Γ₁ ⊢ s ⦂ (τ₁ ∷ [ τ₂ ]) ↦ τ₃ →
      Γ₂ ⊢ t ⦂ τ₁ →
      Γ₃  ⊢ t ⦂ τ₂ →
      (Γ₁ +++ (Γ₂ +++ ( Γ₃ +++ empty))) ⊢ s · t ⦂ τ₃
app₂ s-ok t1-ok t2-ok = app s-ok ( t1-ok ,~ ⋈ctx-refl ∷ ( t2-ok ,~ ⋈ctx-refl ∷ nil)) ⋈ctx-refl


app[] : ∀ {n Γ τ}{s t : term n} →
      Γ ⊢ s ⦂ [] ↦ τ →
      Γ ⊢ s · t ⦂ τ
app[] p = app p nil ⋈ctx-refl-empty

appvar2 : ∀ {σ₁ σ₂ σ τ s} →
     (((nil ,- σ₁) ,-  σ₂) ,- []) ⊢ s ⦂ σ  ↦ τ →
      (((nil ,- σ₁) ,-  σ₂) ,- σ) ⊢ s · (` zero)  ⦂ τ
appvar2 {σ₁} {σ₂} H  = app H var2⊢⦂' ((((nil ,- ⋈++[]) ,- ⋈++[]) ,- ⋈-refl))

appsplit2 : ∀ {σ₁ σ₂ σ₃ σ τ s t} →
     (((nil ,- σ₁) ,-  []) ,- σ₃) ⊢ s ⦂ σ  ↦ τ →
      (((nil ,- []) ,-  σ₂) ,- []) ⊢ t ⦂' σ →
      (((nil ,- σ₁) ,-  σ₂) ,- σ₃) ⊢ s · t  ⦂ τ
appsplit2 Hs Ht = app Hs Ht (((((nil ,- ⋈++[]) ,- ⋈-refl) ,- ⋈++[])))

