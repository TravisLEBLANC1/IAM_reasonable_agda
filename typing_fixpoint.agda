{-# OPTIONS --without-K  #-}

open import Data.Nat using (ℕ; zero; suc; _^_; _*_; _+_; _≤_; _≥_;  z≤n; s≤s; pred)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-identityˡ ; *-identityˡ;  *-identityʳ; *-zeroˡ ;*-zeroʳ; suc-injective; +-suc; *-suc; *-monoʳ-≤; ≤-trans; m≤m+n; +-monoʳ-≤; *-comm; *-assoc)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst; sym; _≢_; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Utils-integers
open import Utils-List
open import Utils-Permut
open import term
open import types




apply-split-2-1 : {N : ℕ} {t : term 3} → {f g : ℕ → type} → (F : (k : ℕ) → (((nil ,- []) ,- ((f (suc (2 * k))) ∷ [ f (2 * k) ])) ,- []) ⊢ t ⦂ (g k)) →
                                         (N ≥ 1) → (((nil ,- []) ,- (applyUpTo f (2 * N))) ,- [])  ⊢ t ⦂' applyUpTo g N
apply-split-2-1 {suc zero} F (s≤s z≤n) = singl⊢ (F 0)
apply-split-2-1 {suc (suc N)} {f = f} {g = g} F (s≤s le)  =  F (suc N) ,~ (((nil ,- nil) ,- skip-≡ lemaux1 (skip-≡ lemaux2 lemaux3)) ,- nil) ∷ apply-split-2-1 F ((s≤s z≤n))
  where
    lemaux1 : f (suc (suc (N + suc (N + zero)))) ≡ f (suc (N + suc (suc (N + zero))))
    lemaux1 rewrite +-suc N (suc (N + 0))  = refl

    lemaux2 : f (suc (N + suc (N + zero))) ≡ f (N + suc (suc (N + zero)))
    lemaux2 rewrite +-suc N (suc (N + 0)) = refl

    lemaux3 : (f (N + suc (N + zero)) ∷ applyUpTo f (N + suc (N + zero))) ⋈ applyUpTo f (N + suc (suc (N + zero)))
    lemaux3 rewrite +-suc N (suc (N + 0)) = ⋈-refl




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
  W1 n m = applyUpTo (λ k → M (m * k) m) (pow-minus1 n) -- the last is indeed m * 2^{n+1} - 2m = 2 * m * (2^n - 1) !

-- M (2 * m * pow-minus1 (n-1))) m :: W2 = W1
  W2 : ℕ → ℕ → List type
  W2 n m = applyUpTo (λ k → M (m * k) m) (pred (pow-minus1  n))

  -- F n m = [ Y i ]_(1 <= i <= m(2^(n+1) -1) ↦ A (m(2^(n+1) -  1))
  F : ℕ → ℕ → type
  F n m = applyUpTo Y  (m * (pow-minus1 n)) ↦ A (m * (pow-minus1 n))


  mutual
    -- Xs n k = [X n k, X (n-1) 2k .. X 0 (2^nk)]
    Xs : ℕ → ℕ →  List type
    Xs 0 k = [ X 0 k ]
    Xs (suc n) k = X (suc n) k ∷ Xs n (2 * k)

    X : ℕ → ℕ → type
    X 0 m = [] ↦ W1 0 m ↦ F 0 m
    X (suc n) m =  Xs n (2 * m) ↦ W1 (suc n) m ↦ F (suc n) m



----- lemmas on the types ------
  W1-0 : ∀ {m} → W1 0 m ≡ [ M 0 m ]
  W1-0 {m} rewrite *-zeroʳ m = refl

  W2-0 : ∀ {m} → W2 1 m ≡ M m m ∷ [ M 0  m ]
  W2-0 {m} rewrite *-zeroʳ m |  *-identityʳ m  = refl

  W2-0' : ∀ {m} → W2 1 m ≡ M (m * 1) m ∷ [ M (m * 0)  m ]
  W2-0' {m} rewrite *-zeroʳ m |  *-identityʳ m  = refl

  W1⋈W2 : {m n : ℕ} → m ≥ 1 → W1 n m ⋈ (M (m * pred (pow-minus1 n)) m  ∷  W2 n m)
  W1⋈W2 {m} {n} le  =  apply-removelast (pow-minus1 n) (pow-≥1 {n})

  Ysuc : {m k : ℕ} →  Y (m + suc k) ≡ [ A (m + suc k) ] ↦ A (suc (m + suc k))
  Ysuc {m} {k} rewrite +-suc m k = refl

  Y'suc : {m k : ℕ} → Y' (m + suc k) ≡ [ A (m + suc k) ]
  Y'suc {zero} = refl
  Y'suc {suc m} = refl

  M-≥1 : {m k : ℕ} → k ≥ 1 → M k m ≡ applyUpTo (λ i → Y (i + k)) m   ↦ [ A k ] ↦ A (m + k)
  M-≥1 (s≤s le) = refl

  M-premium : {m n : ℕ} → m ≥ 1 → M (m * pred (pow-minus1 (suc n))) m ≡
                        applyUpTo (λ i → Y (i + m * pred ( pow-minus1 (suc n)))) m
                          ↦ [ A (m * pred (pow-minus1 (suc n))) ]
                          ↦  A (m * (pow-minus1 (suc n)))
  M-premium {m} {n} le rewrite pow-factor {m} {n} = M-≥1 (lemaux {m} {n} le)
    where
      lemaux' : {n : ℕ} → 2 ≤ 2 * 2 ^ n
      lemaux' {n} = *-monoʳ-≤ 2 (2^n≥1  {n})

      lemaux : {m n : ℕ} → m ≥ 1 → m * pred (pow-minus1 (suc n)) ≥ 1
      lemaux {m} {zero} (s≤s le) =  s≤s z≤n
      lemaux {m} {suc n} (s≤s {m'} le)  =
              ≤-trans (pred≥1 {pow-minus1 (suc (suc n))} (
              ≤-trans (lemaux' {n}) (pow-sucsuc {n}))) (m≤m+n (pred ( pow-minus1 (suc (suc n)))) _)

  F-suc : {n m : ℕ} → F (suc n) (2 * m) ≡ applyUpTo Y (m * pred (pow-minus1 (suc (suc n)))) ↦ A (m * pred (pow-minus1 (suc (suc n))))
  F-suc {n} {m} = cong (λ x → applyUpTo Y x ↦ A x) (sym (pow-factor2m {suc n} {m}))



  type-apply : ∀ {f : ℕ → type} {t : term zero} → (N : ℕ) → (F : (k : ℕ) →  nil ⊢ t ⦂ f k) → nil ⊢ t ⦂' applyUpTo f N
  type-apply zero F = nil
  type-apply (suc N) F = F N ,~ nil ∷ type-apply N F


------- start types lemmas ---------
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

  type-church' : (m : ℕ) → (k : ℕ) → m ≥ 1 →  nil ⊢ church m  ⦂ M k m
  type-church' m k (s≤s {n} {m'} le  )  = type-church m' k

  type-church-multi : (n : ℕ) → (m : ℕ) → m ≥ 1  → nil ⊢ church m  ⦂' W1 n m
  type-church-multi n m le = type-apply (pow-minus1 n) (λ k → type-church' m (m * k) le)

  type-double-zero-aux : (m : ℕ) → (((nil ,-  [ M 0  m ]) ,- applyUpTo (λ i → Y i) m) ,- [])  ⊢
                                            ` suc (suc zero) · ` suc zero ⦂ ([] ↦ A m)
  type-double-zero-aux m  = app (var (suc (suc zero))) var1⊢⦂'   ⋈ctx-refl


  type-double-aux : (m : ℕ) (k : ℕ) → k ≥ 1 → ((((nil ,- [ M k m  ])) ,- applyUpTo (λ i → Y (i + k))  m) ,- []  ) ⊢ ` suc (suc zero) · ` suc zero ⦂ ([ A k ] ↦ A (m + k))
  type-double-aux m k le rewrite M-≥1 {m} {k} le = (app {Γ₁ = Γ₁} {Γ₂ = Γ₂} (var (suc(suc zero))) var1⊢⦂' (((nil ,- ⋈-refl ),- ⋈-refl ),- nil))
    where
      Γ₁ = (((nil ,- [(applyUpTo (λ i → Y' (i + k) ↦ A (suc (i + k))) m ↦ [ A k ] ↦ A (m + k)) ])) ,- []) ,- []

      Γ₂ = (((nil ,- [])) ,- applyUpTo (λ i → Y (i + k))  m ),- []


  type-double-aux' : (m : ℕ) (k : ℕ) → k ≥ 1 → ((((nil ,- [ M k m  ])) ,- applyUpTo (λ i → Y (i + k))  m) ,- [ A k ]  ) ⊢ ` suc (suc zero) · ` suc zero · ` zero ⦂ (A (m + k))
  type-double-aux' m k le = app {Γ₁ = Γ₁} {Γ₂ = Γ₂} (type-double-aux m k le) (singl⊢ (var zero)) Γ⋈ctx
    where
      Γ = (((nil ,- [ M k m  ])) ,- applyUpTo (λ i → Y (i + k))  m) ,- [ A k ]

      Γ₁ = ((nil ,- [ M k m ]) ,- applyUpTo (λ i → Y (i + k))  m) ,- []

      Γ₂ = (((nil ,- [])) ,- [] ),- [ A k ]

      Γ⋈ctx : (Γ₁ +++ Γ₂ )⋈ctx Γ
      Γ⋈ctx rewrite ++-identityʳ (applyUpTo (λ i → Y (i + k)) m) = ⋈ctx-refl

  type-double-zero : (m : ℕ) → m ≥ 1 →  nil  ⊢  double ⦂  (M m  m ∷ [ M 0 m ]) ↦ M 0 (2 * m)
  type-double-zero m le rewrite +-identityʳ m = lam (lam (lam (app {Γ₁ = Γ₁} {Γ₂ = Γ₂} (type-double-aux m m le) (singl⊢ (app[] (type-double-zero-aux m))) Γ⋈ctx)))
    where
      Γ = ((nil ,- (M m m ∷ [ M 0 m ])) ,- applyUpTo Y (m + m )) ,- []

      Γ₁ = (((nil ,- [ M m m  ])) ,- applyUpTo (λ i → Y (i + m))  m) ,- []

      Γ₂ = (((nil ,- [ M 0 m ])) ,- applyUpTo Y  m ),- []

      Γ⋈ctx : (Γ₁ +++ Γ₂ )⋈ctx Γ
      Γ⋈ctx rewrite +-identityʳ m = ((nil ,- ⋈-refl ) ,- apply-split+' m m ) ,- nil

  -- ------- typing the function double -----
  type-double :(m : ℕ) (k : ℕ)  → m ≥ 1 →  nil  ⊢  double ⦂  (M (m * (suc k)) m ∷ [ M (m * k) m  ] ) ↦ M (m * k) (2 * m)
  type-double m zero le rewrite *-zeroʳ m | *-zeroʳ (2 * m)  | *-identityʳ m = type-double-zero m le
  type-double m (suc k) le rewrite M-≥1 {2 * m} {m * suc k} (m*suc≥1 le) | +-identityʳ m  = lam (lam (lam (app {σ = [ A (m + m * (suc k))]} {Γ₁ = Γ₁} {Γ₂ = Γ₂}  (lemaux) (singl⊢ (type-double-aux' m (m * suc k) (m*suc≥1 le))) Γ⋈ctx)))
    where
      Γ = (((nil ,- (M (m * suc (suc k)) m  ∷ [ M (m * (suc k)) m  ])) ,-  applyUpTo (λ i → Y (i + m * (suc k))) (m + m))
                       ,- [ A (m * (suc k)) ])

      Γ₁ =  ((nil ,-  [ M (m * (suc (suc k))) m ]) ,- applyUpTo (λ i → Y (i + m * (suc (suc k)))) m) ,- []

      Γ₂ = ((nil ,-  [ M (m * (suc k)) m ]) ,- applyUpTo (λ i → Y (i + m * (suc k))) m) ,- [ A (m * (suc k)) ]

      -- Γ₃ = ((nil ,-  [ M (m * k) m ]) ,- applyUpTo (λ i → Y (i + m * k)) m) ,- []
      arith-lemma : ∀ {Y : ℕ → type} {i m k : ℕ} → Y ((i + m) + m * suc k) ≡ Y (i + m * suc (suc k))
      arith-lemma {Y} {i} {m} {k} rewrite +-assoc i m (m * suc k) | sym (*-suc m (suc k)) = refl

      lemaux' : (applyUpTo (λ i → Y (i + m * suc (suc k))) m ++ applyUpTo (λ i → Y (i + m * suc k)) m)
           ⋈ applyUpTo (λ i → Y (i + m * suc k)) (m + m)
      lemaux' = ⋈-≡ (sym eq-proof)
        where
          eq-proof : applyUpTo (λ i → Y (i + m * suc k)) (m + m)
                               ≡ (applyUpTo (λ i → Y (i + m * suc (suc k))) m ++ applyUpTo (λ i → Y (i + m * suc k)) m)
          eq-proof =
            begin
            applyUpTo (λ i → Y (i + m * suc k)) (m + m) ≡⟨ apply-split+''  m m ⟩
            applyUpTo (λ i → Y ((i + m) + m * suc k)) m ++ applyUpTo (λ i → Y (i + m * suc k)) m
                     ≡⟨ cong (_++ applyUpTo (λ i → Y (i + m * suc k)) m) (apply-cong m λ i → arith-lemma {Y} {i}) ⟩
            applyUpTo (λ i → Y (i + m * suc (suc k))) m ++ applyUpTo (λ i → Y (i + m * suc k)) m ∎

      Γ⋈ctx : (Γ₁  +++  Γ₂) ⋈ctx Γ
      Γ⋈ctx = ((nil ,- ⋈-refl) ,-  lemaux' ) ,- ⋈-refl

      lemaux : Γ₁ ⊢ ` suc (suc zero) · ` suc zero ⦂ ([ A (m + m * suc k) ] ↦ A (m + m + m * suc k))
      lemaux rewrite *-suc m (suc k) | +-assoc m m (m * suc k) = type-double-aux m (m + m * suc k) (≤-trans le (m≤m+n m (m * suc k)))

  type-doublem-aux : (m : ℕ) (k : ℕ)  → m ≥ 1 → (((nil ,- []) ,- ( M (m * (suc k)) m  ∷ [ M (m * k) m ])) ,- [])  ⊢  lift (double) · (` suc zero) ⦂  M (m * k) (2 * m)
  type-doublem-aux m k le = app₂ (lift⊢ ( type-double m k le )) (var (suc zero)) (var (suc zero))

  type-doublem-aux-zero : (m : ℕ)  → m ≥ 1 → (((nil ,- []) ,- ( M m m  ∷ [ M 0 m ])) ,- [])  ⊢  lift (double) · (` suc zero) ⦂  M 0 (2 * m)
  type-doublem-aux-zero m le = app₂ (lift⊢ (type-double-zero m le)) (var (suc zero)) (var (suc zero))

  ------- typing the term double m ---------
  type-doublem : (m : ℕ) (n : ℕ) → m ≥ 1 → (((nil ,- []) ,- (W2 (suc n) m)) ,- [] )  ⊢  (lift double · (` suc zero)) ⦂'  (W1 n (2 * m))
  type-doublem m zero  le rewrite W1-0 {2 * m} | W2-0 {m} = singl⊢ (type-doublem-aux-zero m le)
  type-doublem m (suc n) le = lemaux FF (pow-≥1 {suc n}) (pow-factor2 {suc n})
    where
      lemaux1 :(m k : ℕ)  → 2 * m * k ≡ m * (2 * k)
      lemaux1 m k rewrite *-comm 2 m | *-assoc m 2 k = refl

      FF : (k : ℕ) → (((nil ,- []) ,- (M (m * suc (2 * k)) m ∷ [ M (m * (2 * k)) m ])) ,- [])
                                     ⊢ lift double · ` suc zero ⦂ M (2 * m * k) (2 * m)
      FF k rewrite lemaux1 m k = type-doublem-aux m (2 * k) le

      lemaux : {N M : ℕ} {t : term 3} → {f g : ℕ → type} → (F : (k : ℕ) → (((nil ,- []) ,- ((f (suc (2 * k))) ∷ [ f (2 * k) ])) ,- []) ⊢ t ⦂ (g k)) →
                         (N ≥ 1) → (M ≡ 2 * N) → (((nil ,- []) ,- (applyUpTo f M)) ,- [])  ⊢ t ⦂' applyUpTo g N
      lemaux F le refl = apply-split-2-1 F le

  type-xx : (m : ℕ) (n : ℕ) → m ≥ 1 → (((nil ,- Xs n (2 * m)) ,- []) ,- []) ⊢ ` suc (suc zero) · ` suc (suc zero) ⦂
      (W1 n (2 * m)) ↦ applyUpTo Y (m * pred (pow-minus1 (suc n))) ↦ A (m * pred (pow-minus1 (suc n)))
  type-xx m 0 le rewrite trans (*-comm m (pred 3)) refl | *-identityʳ (2 * m) = app[] (var (suc (suc zero)))
  type-xx m (suc n)  le  = app {Γ₁ = Γ₁}  {Γ₂ = Γ₂} (lemaux) var3⊢⦂' Γ⋈ctx
    where
      Γ     = ((nil ,- (X (suc n) (2 * m) ∷ Xs n (2 * (2 * m)))) ,- []) ,- []

      Γ₁ = ((nil ,- [ X (suc n) (2 * m) ]) ,- []) ,- []

      Γ₂ = ((nil ,- Xs n (2 * (2 * m))) ,- []) ,- []

      Γ⋈ctx : (Γ₁  +++  Γ₂) ⋈ctx Γ
      Γ⋈ctx  = ((nil ,- ⋈-refl) ,-  nil ) ,- nil

      lemaux : Γ₁  ⊢ ` suc (suc zero) ⦂ Xs n (2 * (2 * m)) ↦ (W1 (suc n) (2 * m)) ↦ applyUpTo Y (m * pred (pow-minus1 (suc (suc n)))) ↦ A (m * pred (pow-minus1 (suc (suc n))))
      lemaux  rewrite F-suc {n} {m} = var (suc (suc  zero))

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
  type-theta (suc n) m le =  lam (lam (lam (app {Γ₁ = Γ₁} {Γ₂ = Γ₂} type-theta-aux1 (singl⊢ type-theta-aux2) Γ⋈ctx )))
   where
       Γ = (((nil ,- Xs n (2 * m)) ,- W1 (suc n) m) ,- applyUpTo Y (m * pow-minus1 (suc n)))

       Γ₁ =  ((nil ,- []) ,-  [ M (m * pred (pow-minus1 (suc n))) m ] ),- applyUpTo (λ i → Y (i +  m * pred (pow-minus1  (suc n)))) m

       Γ₂ =  ((nil ,- Xs n (2 * m)) ,- W2 (suc n) m) ,- applyUpTo Y (m * pred (pow-minus1 (suc n)))
       Γ₃  = ((nil ,- []) ,- [ M (m * pred (pow-minus1  (suc n))) m ]) ,- []
       Γ₄ =  ((nil ,- []) ,- []) ,- applyUpTo (λ i → Y (i +  m * pred (pow-minus1 (suc n)))) m

       Γ⋈ctx :  (Γ₁  +++ Γ₂)  ⋈ctx  Γ
       Γ⋈ctx = ((nil ,-  ⋈-refl )  ,- ⋈-sym (W1⋈W2 {m} {suc n} le)) ,-   apply-split-pred m _ (pow-≥1 {(suc n)})


       type-theta-aux1 :  Γ₁  ⊢ ` suc zero · ` zero ⦂ [ A ( m * pred (pow-minus1 (suc n))) ] ↦ A (m * pow-minus1 (suc n))
       type-theta-aux1 = app {Γ₁ = Γ₃} {Γ₂ = Γ₄}
                          (var (suc (zero2⦂≡ (M-premium {m} {n} le)))) var2⊢⦂' ⋈ctx-refl

       type-theta-aux2 : Γ₂ ⊢ ` suc (suc zero) · ` suc (suc zero) · (lift double · ` suc zero) · ` zero
                                                                          ⦂ A (m * pred ((2 ^ n) + ((2 ^ n) + zero) + pow-minus1 n))
       type-theta-aux2 = appvar2 (appsplit2 {σ = W1 n (2 * m)} (type-xx m n le) (type-doublem m n le))

  type-theta-multi : (n m : ℕ) → m ≥ 1 → nil ⊢ theta ⦂' Xs n m
  type-theta-multi zero m le = singl⊢ (type-theta zero m le)
  type-theta-multi(suc n)  m le = (type-theta (suc n) m le) ,~ nil ∷ (type-theta-multi n (2 * m) (2*m≥1 le))

  type-omegam :(n m : ℕ) → m ≥ 1 →  nil ⊢ theta  · theta · (church m)⦂ F n m
  type-omegam 0 m le = app (app[] (type-theta 0 m le)) (type-church-multi 0 m  le) nil
  type-omegam (suc n) m le = app (app (type-theta (suc n) m le) (type-theta-multi n (2 * m) (2*m≥1 le)) nil) (type-church-multi (suc n) m  le) nil

  type-omega : (n : ℕ) → nil ⊢ omega ⦂ F n 1
  type-omega n = type-omegam n 1 (s≤s z≤n)
