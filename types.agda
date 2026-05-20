
{-# OPTIONS --without-K  #-}

open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _≤_; _≥_;  z≤n; s≤s; pred)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-identityˡ ; *-identityˡ;  *-identityʳ; *-zeroˡ ;*-zeroʳ; suc-injective; +-suc; *-suc)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Axiom.Extensionality.Propositional using (Extensionality ; ExtensionalityImplicit )

-- todo: remove ext (not really needed I think)
postulate
  ext : Extensionality (Agda.Primitive.lzero) (Agda.Primitive.lzero)


applyUpTo : {A : Set} →  (ℕ → A) → ℕ → List A
applyUpTo f zero    = []
applyUpTo f (suc n) = f n ∷ applyUpTo f n


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



module permutations {X : Set} where
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

open permutations


data _⋈ctx_ : ∀ {n} → ctx n → ctx n → Set where
  nil : nil ⋈ctx nil
  _,-_ : ∀ {n}{Γ₁ Γ₂ : ctx n}{σ₁ σ₂} → Γ₁ ⋈ctx Γ₂ → σ₁ ⋈ σ₂ → (Γ₁ ,- σ₁) ⋈ctx (Γ₂ ,- σ₂)

⋈ctx-refl : ∀ {n}{Γ : ctx n} → Γ ⋈ctx Γ
⋈ctx-refl {Γ = nil}    = nil
⋈ctx-refl {Γ = Γ ,- σ} = ⋈ctx-refl ,- ⋈-refl




⋈ctx-refl-empty : ∀ {n}{Γ : ctx n} → (Γ +++ empty)  ⋈ctx Γ
⋈ctx-refl-empty {n} {Γ} = subst (λ x → x ⋈ctx Γ) (sym +++empty) ⋈ctx-refl

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

lift⊢ : ∀ {A} →{n : ℕ} → {t : term zero} →  nil  ⊢ t ⦂ A → empty {n}  ⊢ lift {n} t ⦂ A
lift⊢  d = {!!}

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



--- λf. λx. f x
example₁ : term 0
example₁ = ƛ (ƛ (` (suc zero) · ` zero))

-- λf. λx. f (f x)
example₂ : term 0
example₂ = ƛ (ƛ (` (suc zero) · (` (suc zero) · ` zero)))


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

typing₁ : nil ⊢ example₁ ⦂ [ [ ⋆ ] ↦ ⋆ ] ↦ [ ⋆ ] ↦ ⋆
typing₁ = lam (lam (app₁ (var (suc zero)) (var zero)))


typing₂ : nil ⊢ example₂ ⦂ ([ ⋆ ] ↦ ⋆ ∷ [ ⋆ ] ↦ ⋆ ∷ []) ↦ [ ⋆ ] ↦ ⋆
typing₂ = lam (lam (app₁ (var (suc zero)) (app₁ (var (suc zero)) (var zero))))



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
theta = ƛ (ƛ (ƛ (` (suc zero) · ` zero · (` (suc (suc zero)) · ` (suc (suc zero)) · ((lift double) ·  (` (suc zero)) · ` zero)))))

-- The inlining fixpoint
omega : term zero
omega = theta · theta · one



------------ Types ----------------
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


-- apply-+-suc : ∀ {B : Set} (f : ℕ → B) m k →
--                                applyUpTo (λ i → f (suc (i + k))) m ≡ applyUpTo (λ i → f (i + suc k)) m
-- apply-+-suc f zero k = refl
-- apply-+-suc f (suc m) k = cong (f (suc k) ∷_) (apply-+-suc (λ x → f (suc x)) m k)

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

apply-split-pred : ∀ {B} {f : ℕ → B} (m : ℕ) (k : ℕ)→ k ≥ 1 → (applyUpTo (λ i → f (i + m * (pred k))) m ++ applyUpTo f (m * pred k)) ⋈ applyUpTo f (m * k)
apply-split-pred {f = f} m (suc k') (s≤s le) rewrite *-suc m k' | +-comm m (m * k') =
    applyUpTo (λ i → f (i + m * k')) m ++ applyUpTo f (m * k')   ⋈⟨ ⋈-comm (applyUpTo (λ i → f (i + m * k')) m) (applyUpTo f (m * k')) ⟩
    applyUpTo f (m * k') ++ applyUpTo (λ i → f (i + m * k')) m   ⋈⟨ ⋈-sym (apply-split+ (m * k') m) ⟩
    applyUpTo f (m * k' + m) ■


-- apply-exchange : ∀ {B} {f : ℕ → B} (m : ℕ) → (f m ∷ applyUpTo f m) ⋈ (f 0 ∷ applyUpTo (λ i → f (suc i)) m)
-- apply-exchange m = ⋈-trans (apply-addlast m) ⋈-refl

applyUpTo-ext : {A : Set} (f g : ℕ → A) (n : ℕ)
              → (∀ i → f i ≡ g i)
              → applyUpTo f n ≡ applyUpTo g n
applyUpTo-ext f g zero eq = refl
applyUpTo-ext f g (suc n) eq rewrite eq n | applyUpTo-ext f g n eq = refl

module _ {A : ℕ → type } where
  Y' : ℕ → List type
  Y' zero = []
  Y' (suc k) = [ A (suc k) ]

  Y :  ℕ → type
  Y k = Y' k ↦ A (suc k)

  -- M k m = [Y (k + i)]_(0 <= i <= m)  ↦ [ A k ] ↦ A (m + k)
  M :  ℕ →  ℕ  →  type
  M 0 m = applyUpTo (λ i → Y i) m   ↦ [] ↦ A (m)
  M (suc k) m = applyUpTo (λ i → Y (i + (suc k))) m   ↦ [ A (suc k) ] ↦ A (m + (suc k))

  -- W1 n m == [M (m2 ^ (n+1) - km) m ]_2 <= k <= 2^(n+1)
  W1 : ℕ → ℕ → List type
  W1 n m = applyUpTo (λ k → M (m * k) m) (pow-minus1 (n)) -- the last is indeed m * 2^{n+1} - 2m !

-- M (m * pred (pow-minus1 n)) m :: W2 = W1
  W2 : ℕ → ℕ → List type
  W2 n m = applyUpTo (λ k → M (m * k) m) (pred (pow-minus1 n) )

  -- F n m = [ Y i ]_(1 <= i <= m(2^(n+1) -1) ↦ A (m(2^(n+1) -  1))
  F : ℕ → ℕ → type
  F n m = applyUpTo (λ k → Y  k) (m * (pow-minus1 n)) ↦ A (m * (pow-minus1 n))


  mutual
    -- Xs n k = [X n k, X (n-1) 2k .. X 0 (2^nk)]
    Xs : ℕ → ℕ →  List type
    Xs 0 k = [ X 0 k ]
    Xs (suc n) k = X (suc n) k ∷ Xs n (2 * k)

    X : ℕ → ℕ → type
    X 0 m = [] ↦ W1 0 m ↦ F 0 m
    X (suc n) m =  Xs n 2 ↦ W1 n m ↦ F n m



----- lemmas on the types ------
  W1-0 : ∀ {m} → W1 0 m ≡ [ M 0 m ]
  W1-0 {m} rewrite *-zeroʳ m = refl

  W2-0 : ∀ {m} → W2 1 m ≡ M m m ∷ [ M 0  m ]
  W2-0 {m} rewrite *-zeroʳ m |  *-identityʳ m  = refl

  W1⋈W2 : {m n : ℕ} → m ≥ 1 → W1 n m ⋈ (M (m * pred (pow-minus1 n)) m  ∷  W2 n m)
  W1⋈W2 {m} {n} le  =  apply-removelast (pow-minus1 n) (pow-≥1 {n})

  Ysuc : {m k : ℕ} →  Y (m + suc k) ≡ [ A (m + suc k) ] ↦ A (suc (m + suc k))
  Ysuc {m} {k} rewrite +-suc m k = refl

  Y'suc : {m k : ℕ} → Y' (m + suc k) ≡ [ A (m + suc k) ]
  Y'suc {zero} = refl
  Y'suc {suc m} = refl

  type-church-aux : (m : ℕ) → (k : ℕ) → ((nil  ,-  (applyUpTo (λ i → Y (i + k))(suc  m))) ,-  Y' k) ⊢ church-aux (suc m)  ⦂  A (suc m + k)
  type-church-aux (zero) zero = app[] (var (suc zero))
  type-church-aux (zero) (suc k) = app (var (suc zero)) (singl⊢ (var zero)) ⋈ctx-refl
  type-church-aux (suc m) k  = app (var (suc (zero))) (singl⊢ (type-church-aux m k)) ⋈ctx-refl

  type-church-aux0 : (m : ℕ) → ((nil  ,-  (applyUpTo (λ i → Y i)(suc  m))) ,-  []) ⊢ church-aux (suc m)  ⦂  A (suc m)
  type-church-aux0 (zero) = app[] (var (suc zero))
  type-church-aux0 (suc m) = app (var (suc (zero))) (singl⊢ (type-church-aux0 m)) ⋈ctx-refl

  ------ typing church numerals --------
  type-church : (m : ℕ) → (k : ℕ)  → nil ⊢ church (suc m)  ⦂ M k (suc m)
  type-church m zero = lam (lam (type-church-aux0 m))
  type-church m (suc k) = lam (lam (type-church-aux m (suc k)))



  type-double-aux' : (m : ℕ) (k : ℕ) → (((nil ,-  [ M (m *  k) m ]) ,- applyUpTo (λ i → Y (i + m * k)) m) ,- [])  ⊢
                                            ` suc (suc zero) · ` suc zero ⦂ ([ A (m * k) ] ↦ A (m + m * k))
  type-double-aux' m k = app (var (suc (suc zero))) var1⊢⦂'   {!!}


  type-double-aux : (m : ℕ) (k : ℕ) → (((nil ,-  [ M (m *  k) m ]) ,- applyUpTo (λ i → Y (i + m * k)) m) ,- [])  ⊢
                                            ` suc (suc zero) · ` suc zero ⦂ ([ A (m * k) ] ↦ A (m * (suc k)))
  type-double-aux m k = subst (λ x → (((nil ,-  [ M (m *  k) m ]) ,- applyUpTo (λ i → Y (i + m * k)) m) ,- [])  ⊢
                                            ` suc (suc zero) · ` suc zero ⦂ ([ A (m * k) ] ↦ A x)) (sym (*-suc m k)) (type-double-aux' m k)


  type-double-zero : (m : ℕ) → m ≥ 1 →  nil  ⊢  double ⦂  (M 0 m ∷ [ M m  m ]) ↦ M 0 (2 * m)
  type-double-zero m le = lam (lam (lam {!!}))
    where
      Γ = ((nil ,- (applyUpTo Y m ↦ [] ↦ A m ∷ [ M m m ])) ,- applyUpTo Y (m + (m + zero))) ,- []

      Γ₁ = (((nil ,- [ M m m  ])) ,- applyUpTo (λ i → Y (i + m))  m) ,- []

      Γ₂ = (((nil ,- [ M 0 m ])) ,- applyUpTo Y  m ),- []

      Γ⋈ctx : (Γ₁ +++ Γ₂ )⋈ctx Γ
      Γ⋈ctx = {!!}

  -- ------- typing the function double -----
  type-double :(m : ℕ) (k : ℕ)  → m ≥ 1 →  nil  ⊢  double ⦂  (M (m * k) m ∷ [ M (m * (suc k)) m ]) ↦ M (m * k) (2 * m)
  type-double m zero le rewrite *-zeroʳ m | *-identityʳ m = type-double-zero m le
  type-double m (suc k) (s≤s le) rewrite *-suc m k = lam (lam (lam (app {Γ₁ = Γ₁} {Γ₂ = Γ₂} {!!} {!!} {!!}))) --lam (lam (lam (app s-ok  (singl⊢ t-ok) Γ⋈ctx)))
    where
      Γ = (((nil ,- (M (m * k) m ∷ [ M (m * suc k) m ])) ,-  applyUpTo (λ i → Y (i + m * k)) (2 * m))
                       ,- [ A (m * k) ])

      Γ₁ =  ((nil ,-  [ M (m * (suc k)) m ]) ,- applyUpTo (λ i → Y (i + m * (suc k))) m) ,- []

      Γ₂ = ((nil ,-  [ M (m * k) m ]) ,- applyUpTo (λ i → Y (i + m * k)) m) ,- [ A (m * k) ]

      -- Γ₃ = ((nil ,-  [ M (m * k) m ]) ,- applyUpTo (λ i → Y (i + m * k)) m) ,- []

      Γ⋈ctx : (Γ₁  +++  Γ₂) ⋈ctx Γ
      Γ⋈ctx  = ((nil ,- swap) ,-  ⋈-trans (⋈-≡ (cong (λ f → applyUpTo f m ++ applyUpTo (λ i → Y (i + m * k)) m)
             (ext (λ i → cong Y (begin
                i + m * suc k       ≡⟨ cong (i +_) (*-suc m k) ⟩
                i + (m + m * k)     ≡⟨ sym (+-assoc i m (m * k)) ⟩
                (i + m) + m * k     ≡⟨ cong (_+ m * k) (+-comm i m) ⟩
                m + i + m * k       ∎)))))
         ({!!})) ,- ⋈-refl


  type-doublem-aux : (m : ℕ) (k : ℕ)  → m ≥ 1 →  (nil ,- (M (m * k) m ∷ [ M (m * (suc k)) m ]))  ⊢  lift (double) · (` zero) ⦂  M (m * k) (2 * m)
  type-doublem-aux m k le = app₂ (lift⊢ (type-double m k le)) (var zero) (var zero)



  ------- typing the term double m ---------
  -- type-doublem : (m : ℕ) (n : ℕ)  → (nil ,- (W2 (suc n) m))  ⊢  (lift double · (` zero)) ⦂'  (W1 n (2 * m))
  -- type-doublem m zero  = {!!}
  --              subst (λ r → (nil ,- r) ⊢ lift double · ` zero ⦂' W1 0 (2 * m)) (sym W2-0)
  --              (subst (λ r → (nil ,- (M 0 m ∷ [ M m m ])) ⊢ lift double · ` zero ⦂' r) (sym W1-0)
  --               (singl⊢
  --                 (subst (λ x → (nil ,- (M x m ∷ [ M m m ])) ⊢ lift double · ` zero ⦂ M x (2 * m)) (*-zeroʳ m)
  --                   (subst (λ y → (nil ,- (M (m * 0) m ∷ [ M y m ])) ⊢ lift double · ` zero ⦂ M (m * 0) (2 * m))
  --                     (trans (*-suc m zero) (trans (cong (m +_) (*-zeroʳ m)) (+-identityʳ m)))
  --                       (type-doublem_aux m zero)))))
  -- type-doublem m (suc n) = {!!}



  ------- typing the term theta ---------
  type-theta :(n m : ℕ) → m ≥ 1 →  nil ⊢ theta ⦂ X n m
  type-theta zero m le  = lam (lam (lam (app[] (  app {Γ₁ = Γ₁} {Γ₂ = Γ₂} (var (suc (zero' le))) var2⊢⦂' lemaux)) ))
    where
      Γ₁ = ((nil ,- []) ,- W1 0 m ),- []

      Γ₂ = ((nil ,- []) ,- [] ) ,- ( applyUpTo (λ i → Y i) (m * 1) )

      lemaux : (Γ₁ +++ Γ₂) ⋈ctx (((nil ,- []) ,- W1 0 m ) ,- applyUpTo Y (m * 1))
      lemaux rewrite +-identityʳ m = ⋈ctx-refl

      zero' : {m : ℕ} → m ≥ 1 →  ((nil ,- []) ,- W1 0 m) ⊢v zero ⦂ ((applyUpTo (λ i → Y i) (m * 1)) ↦ [] ↦ A (m * 1))
      zero' {m} le rewrite *-identityʳ m |  *-zeroʳ m = zero
  type-theta (suc n) m le =  lam (lam (lam (app {Γ₁ = Γ₁} {Γ₂ = Γ₂} type-theta-aux1 (singl⊢ {!!}) Γ⋈ctx )))
   where
       Γ = (((nil ,- Xs n 2) ,- W1 n m) ,- applyUpTo Y (m * pow-minus1 n))

       Γ₁ =  ((nil ,- []) ,-  [ M (m * (pred (pow-minus1 n))) m ] ),- applyUpTo (λ i → Y (i + m * (pred (pow-minus1 n)))) m

       Γ₂ =  ((nil ,- Xs n 2) ,- W2 n m) ,- applyUpTo Y (m * pred (pow-minus1 n))

       lemaux : {m n : ℕ}→   (applyUpTo (λ i → Y (i + m * pred (pow-minus1 n))) m
                                                                     ++ applyUpTo Y (m * pred (pow-minus1 n)))
                                                                  ⋈ applyUpTo Y (m * pow-minus1 n)
       lemaux  {m} {n} = apply-split-pred m (pow-minus1 n) (pow-≥1 {n} )

       Γ⋈ctx :  (Γ₁  +++ Γ₂)  ⋈ctx  Γ
       Γ⋈ctx = ((nil ,-  ⋈-refl )  ,- ⋈-sym (W1⋈W2 {m} {n} le)) ,-  lemaux {m} {n}


       type-theta-aux1 :  Γ₁  ⊢ ` suc zero · ` zero ⦂ [ A (m * pred (pow-minus1 n)) ] ↦ A (m * pow-minus1 n)
       type-theta-aux1 = app {Γ₁ = ((nil ,- []) ,- [ M (m * pred (pow-minus1 n)) m ]) ,- []}
                          {Γ₂ = ((nil ,- []) ,- []) ,- applyUpTo (λ i → Y (i + m * (pred (pow-minus1 n)))) m}
                          (var (suc {!zero!})) var2⊢⦂' ⋈ctx-refl  -- problem if n  = 0 ....

       -- lemaux {m} {0} le rewrite *-identityʳ m | *-zeroʳ m = {!⋈-refl!}
       -- lemaux {m} {suc n} le = {!!}
