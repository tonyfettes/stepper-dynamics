open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≤_; _>_; _<_; s≤s; z≤n)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
import Relation.Nullary.Decidable as Dec
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; _≢_; cong₂)
open import Function using (_↔_)

data Act : Set where
  eval : Act
  pause : Act

_≟-act_ : (a₁ : Act) → (a₂ : Act) → Dec (a₁ ≡ a₂)
eval ≟-act eval = yes refl
eval ≟-act pause = no λ ()
pause ≟-act eval = no λ ()
pause ≟-act pause = yes refl

data Gas : Set where
  𝟙 : Gas
  ⋆ : Gas

_≟-gas_ : (g₁ : Gas) → (g₂ : Gas) → Dec (g₁ ≡ g₂)
𝟙 ≟-gas 𝟙 = yes refl
𝟙 ≟-gas ⋆ = no λ ()
⋆ ≟-gas 𝟙 = no λ ()
⋆ ≟-gas ⋆ = yes refl

Id : Set
Id = ℕ

data Pat : Set
data Exp : Set

infix 5 ƛ_
infix 5 φ_⇒_
infix 5 δ_⇒_
infixl 7 _`+_
infixl 8 _`·_
infix 9 #_
infix 9 `_

data Pat where
  $e   : Pat
  $v   : Pat
  `_   : Id → Pat
  !_   : String → Pat
  ƛ_   : Exp → Pat
  _`·_ : Pat → Pat → Pat
  #_   : ℕ → Pat
  _`+_ : Pat → Pat → Pat

_≟-pat_ : (p₁ : Pat) → (p₂ : Pat) → Dec (p₁ ≡ p₂)
_≟-exp_ : (e₁ : Exp) → (e₂ : Exp) → Dec (e₁ ≡ e₂)

$e ≟-pat $e = yes refl
$e ≟-pat $v = no λ ()
$e ≟-pat (` x) = no (λ ())
$e ≟-pat (! x) = no (λ ())
$e ≟-pat (ƛ x) = no (λ ())
$e ≟-pat (p₂ `· p₃) = no (λ ())
$e ≟-pat (# x) = no (λ ())
$e ≟-pat (p₂ `+ p₃) = no (λ ())
$v ≟-pat $e = no (λ ())
$v ≟-pat $v = yes refl
$v ≟-pat (` x) = no (λ ())
$v ≟-pat (! x) = no (λ ())
$v ≟-pat (ƛ x) = no (λ ())
$v ≟-pat (p₂ `· p₃) = no (λ ())
$v ≟-pat (# x) = no (λ ())
$v ≟-pat (p₂ `+ p₃) = no (λ ())
(` x) ≟-pat $e = no (λ ())
(` x) ≟-pat $v = no (λ ())
(` x) ≟-pat (` y) with x Data.Nat.≟ y
(` x) ≟-pat (` y) | yes refl = yes refl
(` x) ≟-pat (` y) | no ¬x≟y = no (λ { refl → ¬x≟y refl })
(` x) ≟-pat (! y) = no λ ()
(` x) ≟-pat (ƛ x₁) = no (λ ())
(` x) ≟-pat (p₂ `· p₃) = no (λ ())
(` x) ≟-pat (# x₁) = no (λ ())
(` x) ≟-pat (p₂ `+ p₃) = no (λ ())
(! x) ≟-pat $e = no (λ ())
(! x) ≟-pat $v = no (λ ())
(! x) ≟-pat (` x₁) = no (λ ())
(! x) ≟-pat (! y) with (x Data.String.≟ y)
... | yes refl = yes refl
... | no x≢y = no λ { refl → x≢y refl }
(! x) ≟-pat (ƛ x₁) = no (λ ())
(! x) ≟-pat (p `· p₁) = no (λ ())
(! x) ≟-pat (# x₁) = no (λ ())
(! x) ≟-pat (p `+ p₁) = no (λ ())
(ƛ x) ≟-pat $e = no (λ ())
(ƛ x) ≟-pat $v = no (λ ())
(ƛ x) ≟-pat (` x₁) = no (λ ())
(ƛ x) ≟-pat (! y) = no λ ()
(ƛ x) ≟-pat (ƛ y) with x ≟-exp y
...               | yes refl = yes refl
...               | no ¬x≟y  = no (λ { refl → ¬x≟y refl })
(ƛ x) ≟-pat (p₂ `· p₃) = no (λ ())
(ƛ x) ≟-pat (# x₁) = no (λ ())
(ƛ x) ≟-pat (p₂ `+ p₃) = no (λ ())
(p₁ `· p₃) ≟-pat $e = no (λ ())
(p₁ `· p₃) ≟-pat $v = no (λ ())
(p₁ `· p₃) ≟-pat (` x) = no (λ ())
(p₁ `· p₃) ≟-pat (! x) = no (λ ())
(p₁ `· p₃) ≟-pat (ƛ x) = no (λ ())
(p₁ `· p₃) ≟-pat (p₂ `· p₄) with (p₁ ≟-pat p₂) with (p₃ ≟-pat p₄)
... | yes refl | yes refl = yes refl
... | yes refl | no ¬3≟4  = no λ { refl → ¬3≟4 refl }
... | no ¬1≟2  | yes _    = no (λ { refl → ¬1≟2 refl })
... | no ¬1≟2  | no _     = no (λ { refl → ¬1≟2 refl })
(p₁ `· p₃) ≟-pat (# x) = no (λ ())
(p₁ `· p₃) ≟-pat (p₂ `+ p₄) = no (λ ())
(# x) ≟-pat $e = no (λ ())
(# x) ≟-pat $v = no (λ ())
(# x) ≟-pat (` x₁) = no (λ ())
(# x) ≟-pat (! x₁) = no (λ ())
(# x) ≟-pat (ƛ x₁) = no (λ ())
(# x) ≟-pat (p₂ `· p₃) = no (λ ())
(# x) ≟-pat (# y) with (x Data.Nat.≟ y)
(# x) ≟-pat (# y) | yes refl = yes refl
(# x) ≟-pat (# y) | no ¬x≟y  = no λ { refl → ¬x≟y refl }
(# x) ≟-pat (p₂ `+ p₃) = no (λ ())
(p₁ `+ p₃) ≟-pat $e = no (λ ())
(p₁ `+ p₃) ≟-pat $v = no (λ ())
(p₁ `+ p₃) ≟-pat (` x) = no (λ ())
(p₁ `+ p₃) ≟-pat (! x) = no (λ ())
(p₁ `+ p₃) ≟-pat (ƛ x) = no (λ ())
(p₁ `+ p₃) ≟-pat (p₂ `· p₄) = no (λ ())
(p₁ `+ p₃) ≟-pat (# x) = no (λ ())
(p₁ `+ p₃) ≟-pat (p₂ `+ p₄) with (p₁ ≟-pat p₂) with (p₃ ≟-pat p₄)
... | yes refl | yes refl = yes refl
... | yes refl | no ¬3≟4  = no λ { refl → ¬3≟4 refl }
... | no ¬1≟2  | yes _    = no (λ { refl → ¬1≟2 refl })
... | no ¬1≟2  | no _     = no (λ { refl → ¬1≟2 refl })

data Exp where
  `_    : (i : Id) → Exp
  !_    : (x : String) → Exp
  ƛ_    : Exp → Exp
  _`·_  : Exp → Exp → Exp
  #_    : ℕ → Exp
  _`+_  : Exp → Exp → Exp
  φ_⇒_ : (f : Pat × Act × Gas) → Exp → Exp
  δ_⇒_ : (r : Act × Gas × ℕ)   → Exp → Exp

(` x) ≟-exp (` y) with (x Data.Nat.≟ y)
... | yes refl = yes refl
... | no x≢y = no λ { refl → x≢y refl }
(` x) ≟-exp (! y) = no (λ ())
(` x) ≟-exp (ƛ e₂) = no (λ ())
(` x) ≟-exp (e₂ `· e₃) = no (λ ())
(` x) ≟-exp (# x₁) = no (λ ())
(` x) ≟-exp (e₂ `+ e₃) = no (λ ())
(` x) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(` x) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(! x) ≟-exp (` x₁) = no (λ ())
(! x) ≟-exp (! y) with (x Data.String.≟ y)
... | yes refl = yes refl
... | no x≢y = no λ { refl → x≢y refl }
(! x) ≟-exp (ƛ e) = no (λ ())
(! x) ≟-exp (e `· e₁) = no (λ ())
(! x) ≟-exp (# x₁) = no (λ ())
(! x) ≟-exp (e `+ e₁) = no (λ ())
(! x) ≟-exp (φ x₁ ⇒ e) = no (λ ())
(! x) ≟-exp (δ x₁ ⇒ e) = no (λ ())
(ƛ e₁) ≟-exp (` x) = no (λ ())
(ƛ e₁) ≟-exp (! x) = no (λ ())
(ƛ e₁) ≟-exp (ƛ e₂) with (e₁ ≟-exp e₂)
... | yes refl = yes refl
... | no e₁≢e₂ = no λ { refl → e₁≢e₂ refl }
(ƛ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(ƛ e₁) ≟-exp (# x) = no (λ ())
(ƛ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(ƛ e₁) ≟-exp (φ x ⇒ e₂) = no (λ ())
(ƛ e₁) ≟-exp (δ x ⇒ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (` x) = no (λ ())
(e₁ `· e₃) ≟-exp (! x) = no (λ ())
(e₁ `· e₃) ≟-exp (ƛ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (e₂ `· e₄) with (e₁ ≟-exp e₂) ×-dec (e₃ ≟-exp e₄)
... | yes (refl , refl) = yes refl
... | no e₁≢e₂ = no λ { refl → e₁≢e₂ (refl , refl) }
(e₁ `· e₃) ≟-exp (# x) = no (λ ())
(e₁ `· e₃) ≟-exp (e₂ `+ e₄) = no (λ ())
(e₁ `· e₃) ≟-exp (φ x ⇒ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (δ x ⇒ e₂) = no (λ ())
(# x) ≟-exp (` x₁) = no (λ ())
(# x) ≟-exp (! x₁) = no (λ ())
(# x) ≟-exp (ƛ e₂) = no (λ ())
(# x) ≟-exp (e₂ `· e₃) = no (λ ())
(# x) ≟-exp (# y) with (x Data.Nat.≟ y)
... | yes refl = yes refl
... | no x≢y = no λ { refl → x≢y refl }
(# x) ≟-exp (e₂ `+ e₃) = no (λ ())
(# x) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(# x) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (` x) = no (λ ())
(e₁ `+ e₃) ≟-exp (! x) = no (λ ())
(e₁ `+ e₃) ≟-exp (ƛ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (e₂ `· e₄) = no (λ ())
(e₁ `+ e₃) ≟-exp (# x) = no (λ ())
(e₁ `+ e₃) ≟-exp (e₂ `+ e₄) with (e₁ ≟-exp e₂) ×-dec (e₃ ≟-exp e₄)
... | yes (refl , refl) = yes refl
... | no e₁≢e₂ = no λ { refl → e₁≢e₂ (refl , refl) }
(e₁ `+ e₃) ≟-exp (φ x ⇒ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (δ x ⇒ e₂) = no (λ ())
(φ x ⇒ e₁) ≟-exp (` x₁) = no (λ ())
(φ x ⇒ e₁) ≟-exp (! x₁) = no (λ ())
(φ x ⇒ e₁) ≟-exp (ƛ e₂) = no (λ ())
(φ x ⇒ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(φ x ⇒ e₁) ≟-exp (# x₁) = no (λ ())
(φ x ⇒ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(φ (p₁ , a₁ , g₁) ⇒ e₁) ≟-exp (φ (p₂ , a₂ , g₂) ⇒ e₂)
    with (p₁ ≟-pat p₂) ×-dec (a₁ ≟-act a₂) ×-dec (g₁ ≟-gas g₂) ×-dec (e₁ ≟-exp e₂)
... | yes (refl , refl , refl , refl) = yes refl
... | no page₁≢page₂ = no (λ { refl → page₁≢page₂ (refl , refl , refl , refl) })
(φ x ⇒ e₁) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(δ x ⇒ e₁) ≟-exp (` x₁) = no (λ ())
(δ x ⇒ e₁) ≟-exp (! x₁) = no (λ ())
(δ x ⇒ e₁) ≟-exp (ƛ e₂) = no (λ ())
(δ x ⇒ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(δ x ⇒ e₁) ≟-exp (# x₁) = no (λ ())
(δ x ⇒ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(δ x ⇒ e₁) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(δ (a₁ , g₁ , l₁) ⇒ e₁) ≟-exp (δ (a₂ , g₂ , l₂) ⇒ e₂)
    with (a₁ ≟-act a₂) ×-dec (g₁ ≟-gas g₂) ×-dec (l₁ Data.Nat.≟ l₂) ×-dec (e₁ ≟-exp e₂)
... | yes (refl , refl , refl , refl) = yes refl
... | no agle₁≢agle₂ = no λ { refl → agle₁≢agle₂ (refl , refl , refl , refl) }

data Value : Exp → Set where
  V-# : ∀ {n : ℕ}
    → Value (# n)

  V-ƛ : ∀ {e}
    → Value (ƛ e)

value? : ∀ (e : Exp) → Dec (Value e)
value? (` x) = no λ ()
value? (! x) = no λ ()
value? (ƛ e) = yes V-ƛ
value? (e `· e₁) = no (λ ())
value? (# x) = yes V-#
value? (e `+ e₁) = no (λ ())
value? (φ x ⇒ e) = no (λ ())
value? (δ x ⇒ e) = no (λ ())

data Normal : Exp → Set where
  N-` : ∀ {x} → Normal (` x)
  N-! : ∀ {x} → Normal (! x)
  N-ƛ : ∀ {e} → Normal e → Normal (ƛ e)
  N-· : ∀ {e₁ e₂} → Normal e₁ → Normal e₂ → Normal (e₁ `· e₂)
  N-# : ∀ {n} → Normal (# n)
  N-+ : ∀ {e₁ e₂} → Normal e₁ → Normal e₂ → Normal (e₁ `+ e₂)

data Filter : Exp → Set where
  F-Φ : ∀ {pag e}
    → Filter (φ pag ⇒ e)

  F-Δ : ∀ {agl e}
    → Filter (δ agl ⇒ e)

filter? : ∀ (e : Exp) → Dec (Filter e)
filter? (` x) = no λ ()
filter? (! x) = no λ ()
filter? (ƛ e) = no λ ()
filter? (e `· e₁) = no λ ()
filter? (# x) = no λ ()
filter? (e `+ e₁) = no λ ()
filter? (φ x ⇒ e) = yes F-Φ
filter? (δ x ⇒ e) = yes F-Δ

data PatVal : Pat → Set where
  PV-# : ∀ {n}
    → PatVal (# n)

  PV-ƛ : ∀ {e}
    → PatVal (ƛ e)

strip : Exp → Exp
strip (` x) = ` x
strip (! x) = ! x
strip (ƛ e) = ƛ (strip e)
strip (e₁ `· e₂) = (strip e₁) `· (strip e₂)
strip (# n) = # n
strip (L `+ M) = (strip L) `+ (strip M)
strip (φ x ⇒ L) = strip L
strip (δ x ⇒ L) = strip L

strip-normal : ∀ (e : Exp) → Normal (strip e)
strip-normal (` x) = N-`
strip-normal (! x) = N-!
strip-normal (ƛ e) = N-ƛ (strip-normal e)
strip-normal (e₁ `· e₂) = N-· (strip-normal e₁) (strip-normal e₂)
strip-normal (# x) = N-#
strip-normal (e₁ `+ e₂) = N-+ (strip-normal e₁) (strip-normal e₂)
strip-normal (φ x ⇒ e) = strip-normal e
strip-normal (δ x ⇒ e) = strip-normal e

patternize : Exp → Pat
patternize (` x) = ` x
patternize (! x) = ! x
patternize (ƛ L) = ƛ L
patternize (L `· M) = (patternize L) `· (patternize M)
patternize (# n) = # n
patternize (L `+ M) = (patternize L) `+ (patternize M)
patternize (φ x ⇒ L) = patternize L
patternize (δ x ⇒ L) = patternize L

[_↦_]_ : ℕ → String → Exp → Exp
[ k ↦ x ] (` i) with (i Data.Nat.≟ k)
... | yes _ = ! x
... | no  _ = ` i
[ k ↦ x ] (! y) = ! y
[ k ↦ x ] (ƛ e) = ƛ [ (ℕ.suc k) ↦ x ] e
[ k ↦ x ] (eₗ `· eᵣ) = ([ k ↦ x ] eₗ) `· ([ k ↦ x ] eᵣ)
[ k ↦ x ] (# n) = # n
[ k ↦ x ] (eₗ `+ eᵣ) = ([ k ↦ x ] eₗ) `+ ([ k ↦ x ] eᵣ)
[ k ↦ x ] (φ pag ⇒ e) = φ pag ⇒ [ k ↦ x ] e
[ k ↦ x ] (δ agl ⇒ e) = δ agl ⇒ [ k ↦ x ] e

[_↤_]_ : ℕ → String → Exp → Exp
[ k ↤ x ] (` i) = ` i
[ k ↤ x ] (! y) with (x Data.String.≟ y)
... | yes _ = ` k
... | no  _ = ! y
[ k ↤ x ] (ƛ e) = ƛ ([ (k + 1) ↤ x ] e)
[ k ↤ x ] (eₗ `· eᵣ) = ([ k ↤ x ] eₗ) `· ([ k ↤ x ] eᵣ)
[ k ↤ x ] (# n) = # n
[ k ↤ x ] (eₗ `+ eᵣ) = ([ k ↤ x ] eₗ) `+ ([ k ↤ x ] eᵣ)
[ k ↤ x ] (φ pag ⇒ e) = φ pag ⇒ [ k ↤ x ] e
[ k ↤ x ] (δ agl ⇒ e) = δ agl ⇒ [ k ↤ x ] e

_[_:=_] : Exp → String → Exp → Exp
_⟨_:=_⟩ : Pat → String → Exp → Pat

$e ⟨ _ := _ ⟩ = $e
$v ⟨ _ := _ ⟩ = $v
(` i) ⟨ _ := _ ⟩ = (` i)
(! x) ⟨ y := v ⟩ with (x Data.String.≟ y)
... | yes refl = patternize v
... | no  _    = (! x)
(ƛ e) ⟨ y := v ⟩      = ƛ (e [ y := v ])
(p₁ `· p₂) ⟨ x := v ⟩ = (p₁ ⟨ x := v ⟩) `· (p₂ ⟨ x := v ⟩)
(# n) ⟨ _ := _ ⟩      = # n
(p₁ `+ p₂) ⟨ x := v ⟩ = (p₁ ⟨ x := v ⟩) `+ (p₂ ⟨ x := v ⟩)

(` i)      [ y := v ] = (` i)
(! x)      [ y := v ] with (x Data.String.≟ y)
...                   | yes refl = v
...                   | no  _    = (! x)
(ƛ e)      [ x := v ] = ƛ (e [ x := v ])
(e₁ `· e₂) [ x := v ] = (e₁ [ x := v ]) `· (e₂ [ x := v ])
(# n)      [ x := v ] = # n
(e₁ `+ e₂) [ x := v ] = (e₁ [ x := v ]) `+ (e₂ [ x := v ])
(φ f ⇒ e) [ x := v ] = φ f ⇒ e [ x := v ]
(δ r ⇒ e) [ x := v ] = δ r ⇒ e [ x := v ]

fv : Exp → List String
fv (` x) = []
fv (! x) = x ∷ []
fv (ƛ e) = fv e
fv (eₗ `· eᵣ) = (fv eₗ) ++ (fv eᵣ)
fv (# x) = []
fv (eₗ `+ eᵣ) = (fv eₗ) ++ (fv eᵣ)
fv (φ f ⇒ e) = fv e
fv (δ r ⇒ e) = fv e

_is-fresh-in_ : String → Exp → Set
x is-fresh-in t = ¬ (x ∈ fv t)

infix 4 _matches_

data _matches_ : Pat → Exp → Set where
  M-E : ∀ {e}
    → $e matches e

  M-V : ∀ {v}
    → Value v
    → $v matches v

  M-· : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ matches eₗ
    → pᵣ matches eᵣ
    → (pₗ `· pᵣ) matches (eₗ `· eᵣ)

  M-+ : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ matches eₗ
    → pᵣ matches eᵣ
    → (pₗ `+ pᵣ) matches (eₗ `+ eᵣ)

  M-ƛ : ∀ {eₚ eₑ}
    → (strip eₚ) ≡ (strip eₑ)
    → (ƛ eₚ) matches (ƛ eₑ)

  M-# : ∀ {n}
    → (# n) matches (# n)

_matches?_ : (p : Pat) → (e : Exp) → Dec (p matches e)
$e matches? e         = yes M-E
$v matches? e with (value? e)
$v matches? e | yes V = yes (M-V V)
$v matches? e | no ¬V = no λ { (M-V V) → ¬V V }
(` x) matches? e = no λ ()
(! x) matches? e = no λ ()
(ƛ x) matches? (` x₁) = no λ ()
(ƛ x) matches? (! x₁) = no λ ()
(ƛ x) matches? (ƛ e) with ((strip x) ≟-exp (strip e))
... | yes pₛ≡eₛ = yes (M-ƛ pₛ≡eₛ)
... | no ¬pₛ≡eₛ = no λ { (M-ƛ pₛ≡eₛ) → ¬pₛ≡eₛ pₛ≡eₛ }
(ƛ x) matches? (e `· e₁) = no (λ ())
(ƛ x) matches? (# x₁) = no λ ()
(ƛ x) matches? (e `+ e₁) = no λ ()
(ƛ x) matches? (φ x₁ ⇒ e) = no λ ()
(ƛ x) matches? (δ x₁ ⇒ e) = no λ ()
(p₁ `· p₂) matches? (` x) = no λ ()
(p₁ `· p₂) matches? (! x) = no λ ()
(p₁ `· p₂) matches? (ƛ e) = no λ ()
(p₁ `· p₂) matches? (e₁ `· e₂) with (p₁ matches? e₁) ×-dec (p₂ matches? e₂)
... | yes (matches₁ , matches₂) = yes (M-· matches₁ matches₂)
... | no ¬matches = no λ { (M-· matches₁ matches₂) → ¬matches (matches₁ , matches₂) }
(p₁ `· p₂) matches? (# x) = no λ ()
(p₁ `· p₂) matches? (e `+ e₁) = no λ ()
(p₁ `· p₂) matches? (φ x ⇒ e) = no λ ()
(p₁ `· p₂) matches? (δ x ⇒ e) = no λ ()
(# x) matches? (` x₁) = no λ ()
(# x) matches? (! x₁) = no λ ()
(# x) matches? (ƛ e) = no λ ()
(# x) matches? (e `· e₁) = no λ ()
(# x) matches? (# y) with (x Data.Nat.≟ y)
... | yes refl = yes M-#
... | no x≢y = no λ { M-# → x≢y refl }
(# x) matches? (e `+ e₁) = no λ ()
(# x) matches? (φ x₁ ⇒ e) = no λ ()
(# x) matches? (δ x₁ ⇒ e) = no λ ()
(p₁ `+ p₂) matches? (` x) = no λ ()
(p₁ `+ p₂) matches? (! x) = no λ ()
(p₁ `+ p₂) matches? (ƛ e) = no λ ()
(p₁ `+ p₂) matches? (e `· e₁) = no λ ()
(p₁ `+ p₂) matches? (# x) = no λ ()
(p₁ `+ p₂) matches? (e₁ `+ e₂) with (p₁ matches? e₁) ×-dec (p₂ matches? e₂)
... | yes (matches₁ , matches₂) = yes (M-+ matches₁ matches₂)
... | no ¬matches = no λ { (M-+ matches₁ matches₂) → ¬matches (matches₁ , matches₂) }
(p₁ `+ p₂) matches? (φ x ⇒ e) = no λ ()
(p₁ `+ p₂) matches? (δ x ⇒ e) = no λ ()

infix 0 _—→_

data _—→_ : Exp → Exp → Set where
  β-· : ∀ {vᵣ eₓ x}
    → Value vᵣ
    → x is-fresh-in eₓ
    → (ƛ eₓ) `· vᵣ —→ (([ 0 ↦ x ] eₓ) [ x := vᵣ ])

  β-+ : ∀ {nₗ nᵣ}
    → (# nₗ) `+ (# nᵣ) —→ (# (nₗ Data.Nat.+ nᵣ))

  β-φ : ∀ {pag v}
    → Value v
    → (φ pag ⇒ v) —→ v

  β-δ : ∀ {agl v}
    → Value v
    → (φ agl ⇒ v) —→ v

data Ctx : Set where
  ∘     : Ctx
  _·ₗ_  : Ctx → Exp → Ctx
  _·ᵣ_  : Exp → Ctx → Ctx
  _+ₗ_  : Ctx → Exp → Ctx
  _+ᵣ_  : Exp → Ctx → Ctx
  φ_⇒_ : Pat × Act × Gas → Ctx → Ctx
  δ_⇒_ : Act × Gas × ℕ → Ctx → Ctx

data _⇒_⟨_⟩ : Exp → Ctx → Exp → Set where
  D-β-` : ∀ {x}
    → (` x) ⇒ ∘ ⟨ (` x) ⟩

  D-ξ-·ₗ : ∀ {eₗ eᵣ ℰ eₗ′}
    → eₗ ⇒ ℰ ⟨ eₗ′ ⟩
    → (eₗ `· eᵣ) ⇒ (ℰ ·ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-·ᵣ : ∀ {vₗ eᵣ ℰ eᵣ′}
    → Value vₗ
    → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
    → (vₗ `· eᵣ) ⇒ (vₗ ·ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-· : ∀ {vₗ vᵣ ℰ}
    → Value vₗ
    → Value vᵣ
    → (vₗ `· vᵣ) ⇒ ℰ ⟨ vₗ `· vᵣ ⟩

  D-ξ-+ₗ : ∀ {eₗ eᵣ ℰ eₗ′}
    → eₗ ⇒ ℰ ⟨ eₗ′ ⟩
    → (eₗ `+ eᵣ) ⇒ (ℰ +ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-+ᵣ : ∀ {vₗ eᵣ ℰ eᵣ′}
    → Value vₗ
    → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
    → (vₗ `+ eᵣ) ⇒ (vₗ +ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-+ : ∀ {vₗ vᵣ ℰ}
    → Value vₗ
    → Value vᵣ
    → (vₗ `+ vᵣ) ⇒ ℰ ⟨ vₗ `+ vᵣ ⟩

  D-ξ-φ : ∀ {pag e ℰ e′}
    → e ⇒ ℰ ⟨ e′ ⟩
    → (φ pag ⇒ e) ⇒ (φ pag ⇒ ℰ) ⟨ e′ ⟩

  D-β-φ : ∀ {pag v ℰ}
    → Value v
    → (φ pag ⇒ v) ⇒ ℰ ⟨ φ pag ⇒ v ⟩

  D-ξ-δ : ∀ {agl e ℰ e′}
    → e ⇒ ℰ ⟨ e′ ⟩
    → (δ agl ⇒ e) ⇒ (δ agl ⇒ ℰ) ⟨ e′ ⟩

  D-β-δ : ∀ {agl v ℰ}
    → Value v
    → (δ agl ⇒ v) ⇒ ℰ ⟨ δ agl ⇒ v ⟩

V¬⇒ : ∀ {v ε e}
  → Value v
  → ¬ (v ⇒ ε ⟨ e ⟩)
V¬⇒ V-# ()
V¬⇒ V-ƛ ()

⇒¬V : ∀ {e ε e₀}
  → e ⇒ ε ⟨ e₀ ⟩
  → ¬ (Value e)
⇒¬V D-β-` ()
⇒¬V (D-ξ-·ₗ _) ()
⇒¬V (D-ξ-·ᵣ _ _) ()
⇒¬V (D-β-· _ _) ()
⇒¬V (D-ξ-+ₗ _) ()
⇒¬V (D-ξ-+ᵣ _ _) ()
⇒¬V (D-β-+ _ _) ()
⇒¬V (D-ξ-φ _) ()
⇒¬V (D-β-φ _) ()
⇒¬V (D-ξ-δ _) ()
⇒¬V (D-β-δ _) ()

data _⇐_⟨_⟩ : Exp → Ctx → Exp → Set where
  C-∘ : ∀ {e}
    → e ⇐ ∘ ⟨ e ⟩

  C-·ₗ : ∀ {εₗ eᵣ eₗ e}
    → eₗ ⇐ εₗ ⟨ e ⟩
    → (eₗ `· eᵣ) ⇐ (εₗ ·ₗ eᵣ) ⟨ e ⟩

  C-·ᵣ : ∀ {eₗ εᵣ eᵣ e}
    → eᵣ ⇐ εᵣ ⟨ e ⟩
    → (eₗ `· eᵣ) ⇐ (eₗ ·ᵣ εᵣ) ⟨ e ⟩

  C-+ₗ : ∀ {εₗ eᵣ eₗ e}
    → eₗ ⇐ εₗ ⟨ e ⟩
    → (eₗ `+ eᵣ) ⇐ (εₗ +ₗ eᵣ) ⟨ e ⟩

  C-+ᵣ : ∀ {eₗ εᵣ eᵣ e}
    → eᵣ ⇐ εᵣ ⟨ e ⟩
    → (eₗ `+ eᵣ) ⇐ (eₗ +ᵣ εᵣ) ⟨ e ⟩

  C-φ : ∀ {pag ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (φ pag ⇒ e′) ⇐ (φ pag ⇒ ε) ⟨ e ⟩

  C-δ : ∀ {agl ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (δ agl ⇒ e′) ⇐ (δ agl ⇒ ε) ⟨ e ⟩

data _⊢_⇝_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  I-V : ∀ {pagl v}
    → Value v
    → pagl ⊢ v ⇝ v

  I-`-⊤ : ∀ {p a g l x}
    → p matches (` x)
    → (p , a , g , l) ⊢ (` x) ⇝ (δ (a , g , l) ⇒ (` x))

  I-`-⊥ : ∀ {p a g l x}
    → ¬ (p matches (` x))
    → (p , a , g , l) ⊢ (` x) ⇝ (` x)

  I-·-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ `· eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (δ (a , g , l) ⇒ (eₗ′ `· eᵣ′))

  I-·-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ `· eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (eₗ′ `· eᵣ′)

  I-+-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ `+ eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `+ eᵣ) ⇝ (δ (a , g , l) ⇒ (eₗ′ `+ eᵣ′))

  I-+-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ `+ eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `+ eᵣ) ⇝ (eₗ′ `+ eᵣ′)

  I-Φ : ∀ {pat act gas lvl p a g e e′ e″}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (p , a , g , ℕ.suc lvl) ⊢ e′ ⇝ e″
    → (pat , act , gas , lvl) ⊢ (φ (p , a , g) ⇒ e) ⇝ (φ (p , a , g) ⇒ e″)

  I-Δ : ∀ {pat act gas lvl a g l e e′}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (pat , act , gas , lvl) ⊢ (δ (a , g , l) ⇒ e) ⇝ (δ (a , g , l) ⇒ e′)

strip-instr : ∀ {p : Pat} {a : Act} {g : Gas} {l : ℕ} {e e′ : Exp}
  → (p , a , g , l) ⊢ e ⇝ e′
  → strip e′ ≡ strip e
strip-instr (I-V _) = refl
strip-instr (I-`-⊤ _) = refl
strip-instr (I-`-⊥ _) = refl
strip-instr (I-·-⊤ _ Iₗ Iᵣ) = Eq.cong₂ _`·_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-·-⊥ _ Iₗ Iᵣ) = Eq.cong₂ _`·_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-+-⊤ _ Iₗ Iᵣ) = Eq.cong₂ _`+_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-+-⊥ _ Iₗ Iᵣ) = Eq.cong₂ _`+_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-Φ I₀ I₁) = Eq.trans (strip-instr I₁) (strip-instr I₀)
strip-instr (I-Δ I) = (strip-instr I)

data _⊢_⇝_⊣_ : Act × ℕ → Ctx → Ctx → Act → Set where
  A-∘ : ∀ {act lvl}
    → (act , lvl) ⊢ ∘ ⇝ ∘ ⊣ act

  A-·-l : ∀ {act lvl εₗ εₗ′ eᵣ act′}
    → (act , lvl) ⊢ εₗ ⇝ εₗ′ ⊣ act′
    → (act , lvl) ⊢ (εₗ ·ₗ eᵣ) ⇝ (εₗ′ ·ₗ eᵣ) ⊣ act′

  A-·-r : ∀ {act lvl eₗ εᵣ εᵣ′ act′}
    → (act , lvl) ⊢ εᵣ ⇝ εᵣ′ ⊣ act′
    → (act , lvl) ⊢ (eₗ ·ᵣ εᵣ) ⇝ (eₗ ·ᵣ εᵣ′) ⊣ act′

  A-+-l : ∀ {act lvl εₗ εₗ′ eᵣ act′}
    → (act , lvl) ⊢ εₗ ⇝ εₗ′ ⊣ act′
    → (act , lvl) ⊢ (εₗ +ₗ eᵣ) ⇝ (εₗ′ +ₗ eᵣ) ⊣ act′

  A-+-r : ∀ {act lvl eₗ εᵣ εᵣ′ act′}
    → (act , lvl) ⊢ εᵣ ⇝ εᵣ′ ⊣ act′
    → (act , lvl) ⊢ (eₗ +ᵣ εᵣ) ⇝ (eₗ +ᵣ εᵣ′) ⊣ act′

  A-Φ : ∀ {act lvl ε ε′ act′ pag}
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ φ pag ⇒ ε ⇝ φ pag ⇒ ε′ ⊣ act′

  A-Δ-1-> : ∀ {act lvl ε ε′ act′ a l}
    → l > lvl
    → (a , l) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , 𝟙 , l) ⇒ ε ⇝ ε′ ⊣ act′

  A-Δ-1-≤ : ∀ {act lvl ε ε′ act′ a l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , 𝟙 , l) ⇒ ε ⇝ ε′ ⊣ act′

  A-Δ-∀-> : ∀ {act lvl ε ε′ act′ a l}
    → l > lvl
    → (a , l) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , ⋆ , l) ⇒ ε ⇝ δ (a , ⋆ , l) ⇒ ε′ ⊣ act′

  A-Δ-∀-≤ : ∀ {act lvl ε ε′ act′ a l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , ⋆ , l) ⇒ ε ⇝ δ (a , ⋆ , l) ⇒ ε′ ⊣ act′

data _⊢_↠_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  skip : ∀ {p a g l e e′ eᵢ e₀ e₀′ ε ε₀}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → Filter e₀ ⊎ (a , l) ⊢ ε₀ ⇝ ε ⊣ eval
    → e₀ —→ e₀′
    → e′ ⇐ ε ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e ↠ e′

infix 0 _⇥_

data _⊢_⇥_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  step : ∀ {p a g l e e′ eᵢ e₀ e₀′ ε ε₀}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → (a , l) ⊢ ε₀ ⇝ ε ⊣ pause
    → e₀ —→ e₀′
    → e′ ⇐ ε ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e ⇥ e′

infixr 7 _⇒_

data Typ : Set where
  _⇒_ : Typ → Typ → Typ
  `ℕ   : Typ

infixl 5 _,_∶_

data TypCtx : Set where
  ∅     : TypCtx
  _,_∶_ : TypCtx → String → Typ → TypCtx

infix 4 _∋_∶_

data _∋_∶_ : TypCtx → String → Typ → Set where
  ∋-Z : ∀ {Γ x τ}
    → Γ , x ∶ τ ∋ x ∶ τ

  ∋-S : ∀ {Γ x₁ x₂ τ₁ τ₂}
    → Γ ∋ x₁ ∶ τ₁
    → Γ , x₂ ∶ τ₂ ∋ x₁ ∶ τ₁

infix 4 _⊢_∶_
infix 5 _⊢_∻_

data _⊢_∶_ : TypCtx → Exp → Typ → Set
data _⊢_∻_ : TypCtx → Pat → Typ → Set

data _⊢_∶_ where
  ⊢-! : ∀ {Γ x τ}
    → Γ ∋ x ∶ τ
    → Γ ⊢ ! x ∶ τ

  ⊢-ƛ : ∀ {Γ e τₓ τₑ L}
    → (∀ x → ¬ (x ∈ L) →
       Γ , x ∶ τₓ ⊢ ([ 0 ↦ x ] e) ∶ τₑ)
    → Γ ⊢ ƛ e ∶ (τₓ ⇒ τₑ)

  ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
    → Γ ⊢ e₁ ∶ (τ₂ ⇒ τ₁)
    → Γ ⊢ e₂ ∶ τ₂
    → Γ ⊢ (e₁ `· e₂) ∶ τ₁

  ⊢-+ : ∀ {Γ e₁ e₂}
    → Γ ⊢ e₁ ∶ `ℕ
    → Γ ⊢ e₂ ∶ `ℕ
    → Γ ⊢ (e₁ `+ e₂) ∶ `ℕ

  ⊢-# : ∀ {Γ n}
    → Γ ⊢ (# n) ∶ `ℕ

  ⊢-φ : ∀ {Γ p τₚ ag e τₑ}
    → Γ ⊢ p ∻ τₚ
    → Γ ⊢ e ∶ τₑ
    → Γ ⊢ φ (p , ag) ⇒ e ∶ τₑ

  ⊢-δ : ∀ {Γ agl e τ}
    → Γ ⊢ e ∶ τ
    → Γ ⊢ δ agl ⇒ e ∶ τ

data _⊢_∻_ where
  ⊢-E : ∀ {Γ τ}
    → Γ ⊢ $e ∻ τ

  ⊢-V : ∀ {Γ τ}
    → Γ ⊢ $v ∻ τ

  ⊢-! : ∀ {Γ x τ}
    → Γ ∋ x ∶ τ
    → Γ ⊢ ! x ∻ τ

  ⊢-ƛ : ∀ {Γ x e τₓ τₑ}
    → Γ , x ∶ τₓ ⊢ ([ 0 ↦ x ] e) ∶ τₑ
    → Γ ⊢ ƛ e ∻ (τₓ ⇒ τₑ)

  ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
    → Γ ⊢ e₁ ∻ τ₂ ⇒ τ₁
    → Γ ⊢ e₂ ∻ τ₂
    → Γ ⊢ (e₁ `· e₂) ∻ τ₁

  ⊢-# : ∀ {Γ n}
    → Γ ⊢ (# n) ∻ `ℕ

  ⊢-+ : ∀ {Γ e₁ e₂}
    → Γ ⊢ e₁ ∻ `ℕ
    → Γ ⊢ e₂ ∻ `ℕ
    → Γ ⊢ (e₁ `+ e₂) ∻ `ℕ

-- ext : ∀ {Γ Δ}
--   → (∀ {x A}   →     Γ ∋ x ∶ A →     Δ ∋ x ∶ A)
--   → (∀ {x A B} → Γ , B ∋ x ∶ A → Δ ⸴ B ∋ x ∶ A)
-- ext ρ ∋-Z       =  ∋-Z
-- ext ρ (∋-S ∋x)  =  ∋-S (ρ ∋x)

-- rename-exp : ∀ {Γ Δ}
--   → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
--   → (∀ {e A} → Γ ⊢ e ∶ A → Δ ⊢ e ∶ A)
-- rename-pat : ∀ {Γ Δ}
--   → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
--   → (∀ {e A} → Γ ⊢ e ∻ A → Δ ⊢ e ∻ A)

-- rename-exp ρ (⊢-` ∋-x)   = ⊢-` (ρ ∋-x)
-- rename-exp ρ (⊢-ƛ ⊢-N)   = ⊢-ƛ (rename-exp (ext ρ) ⊢-N)
-- rename-exp ρ (⊢-· e₁ e₂) = ⊢-· (rename-exp ρ e₁) (rename-exp ρ e₂)
-- rename-exp ρ (⊢-+ e₁ e₂) = ⊢-+ (rename-exp ρ e₁) (rename-exp ρ e₂)
-- rename-exp ρ ⊢-#         = ⊢-#
-- rename-exp ρ (⊢-φ p e)     = ⊢-φ (rename-pat ρ p) (rename-exp ρ e)
-- rename-exp ρ (⊢-δ Γ-⊢)   = ⊢-δ (rename-exp ρ Γ-⊢)

-- rename-pat ρ ⊢-E         = ⊢-E
-- rename-pat ρ ⊢-V         = ⊢-V
-- rename-pat ρ (⊢-` ∋-x)   = ⊢-` (ρ ∋-x)
-- rename-pat ρ (⊢-ƛ x⊢e)   = ⊢-ƛ (rename-exp (ext ρ) x⊢e)
-- rename-pat ρ (⊢-· e₁ e₂) = ⊢-· (rename-pat ρ e₁) (rename-pat ρ e₂)
-- rename-pat ρ ⊢-#         = ⊢-#
-- rename-pat ρ (⊢-+ e₁ e₂) = ⊢-+ (rename-pat ρ e₁) (rename-pat ρ e₂)

-- ∋-functional : ∀ {Γ x τ₁ τ₂} → (Γ ∋ x ∶ τ₁) → (Γ ∋ x ∶ τ₂) → τ₁ ≡ τ₂
-- ∋-functional ∋-Z ∋-Z = refl
-- ∋-functional (∋-S ∋₁) (∋-S ∋₂) = ∋-functional ∋₁ ∋₂

strip-var-open : ∀ (e : Exp) → (k : ℕ) → (x : String)
  → strip ([ k ↦ x ] e) ≡ [ k ↦ x ] (strip e)
strip-var-open (` i) k x with (i Data.Nat.≟ k)
... | yes refl = refl
... | no  _    = refl
strip-var-open (! y) k x = refl
strip-var-open (ƛ e) k x = cong ƛ_ (strip-var-open e (ℕ.suc k) x)
strip-var-open (eₗ `· eᵣ) k x = cong₂ _`·_ (strip-var-open eₗ k x) (strip-var-open eᵣ k x)
strip-var-open (# x₁) k x = refl
strip-var-open (eₗ `+ eᵣ) k x = cong₂ _`+_ (strip-var-open eₗ k x) (strip-var-open eᵣ k x)
strip-var-open (φ f ⇒ e) k x = strip-var-open e k x
strip-var-open (δ r ⇒ e) k x = strip-var-open e k x

strip-preserve : ∀ {Γ e τ}
  → Γ ⊢ e ∶ τ
  → Γ ⊢ (strip e) ∶ τ
strip-preserve (⊢-! ∋-x) = ⊢-! ∋-x
strip-preserve (⊢-ƛ x⊢e) = ⊢-ƛ {!!}
strip-preserve (⊢-· ⊢₁ ⊢₂) = ⊢-· (strip-preserve ⊢₁) (strip-preserve ⊢₂)
strip-preserve (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (strip-preserve ⊢₁) (strip-preserve ⊢₂)
strip-preserve ⊢-# = ⊢-#
strip-preserve (⊢-φ ⊢ₚ ⊢ₑ) = strip-preserve ⊢ₑ
strip-preserve (⊢-δ ⊢ₑ) = strip-preserve ⊢ₑ

instr-preserve : ∀ {Γ e τ p a g l e′}
  → Γ ⊢ e ∶ τ
  → (p , a , g , l) ⊢ e ⇝ e′
  → Γ ⊢ e′ ∶ τ
instr-preserve ⊢ (I-V V) = ⊢
instr-preserve ⊢ (I-`-⊤ x) = ⊢-δ ⊢
instr-preserve ⊢ (I-`-⊥ x) = ⊢
instr-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊤ x Iₗ Iᵣ) = ⊢-δ (⊢-· (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ))
instr-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊥ x Iₗ Iᵣ) = ⊢-· (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ)
instr-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊤ x Iₗ Iᵣ) = ⊢-δ (⊢-+ (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ))
instr-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊥ x Iₗ Iᵣ) = ⊢-+ (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ)
instr-preserve (⊢-φ ⊢ₚ ⊢ₑ) (I-Φ I₀ I₁) = ⊢-φ ⊢ₚ (instr-preserve (instr-preserve ⊢ₑ I₀) I₁)
instr-preserve (⊢-δ ⊢) (I-Δ I) = ⊢-δ (instr-preserve ⊢ I)

-- weaken : ∀ {Γ e A}
--   → ∅ ⊢ e ∶ A
--   → Γ ⊢ e ∶ A
-- weaken {Γ} ⊢e = rename-exp ρ ⊢e
--   where
--   ρ : ∀ {z C}
--     → ∅ ∋ z ∶ C
--     → Γ ∋ z ∶ C
--   ρ ()

-- subst : ∀ {Γ v e x τᵥ τₑ}
--   → ∅ ⊢ v ∶ τᵥ
--   → Γ ⸴ τᵥ ⊢ e ∶ τₑ
--   → Γ ⊢ (e [ x := v ]) ∶ τₑ
-- subst {e = ` ℕ.zero} ⊢ᵥ (⊢-! ∋-Z) = {!!}
-- subst {e = ` (ℕ.suc x)} ⊢ᵥ (⊢-! (∋-S {x = y} ∋)) = ⊥-elim {!!}
-- subst ⊢ᵥ (⊢-ƛ ⊢ₑ) = {!!}
-- subst ⊢ᵥ (⊢-· ⊢ₑ ⊢ₑ₁) = {!!}
-- subst ⊢ᵥ (⊢-+ ⊢ₑ ⊢ₑ₁) = {!!}
-- subst ⊢ᵥ ⊢-# = {!!}
-- subst ⊢ᵥ (⊢-φ x ⊢ₑ) = {!!}
-- subst ⊢ᵥ (⊢-δ ⊢ₑ) = {!!}

—→-preserve : ∀ {Γ e τ e′}
  → Γ ⊢ e ∶ τ
  → e —→ e′
  → Γ ⊢ e′ ∶ τ
—→-preserve (⊢-· ⊢ₗ ⊢ᵣ) (β-· Vᵣ x) = {!!}
—→-preserve (⊢-+ ⊢ ⊢₁) T = {!!}
—→-preserve (⊢-φ x ⊢) T = {!!}

data Progress_under_ : Exp → Pat × Act × Gas × ℕ → Set where
  step : ∀ {p a g l e₀ e₁}
    → (p , a , g , l) ⊢ e₀ ⇥ e₁
    → Progress e₀ under (p , a , g , l)

  skip : ∀ {p a g l e₀ e₁}
    → (p , a , g , l) ⊢ e₀ ↠ e₁
    → Progress e₀ under (p , a , g , l)

  done : ∀ {p a g l v}
    → Value v
    → Progress v under (p , a , g , l)

progress : ∀ {p a g l e τ}
  → ∅ ⊢ e ∶ τ
  → Progress e under (p , a , g , l)
progress (⊢-ƛ ⊢) = done V-ƛ
progress {p = p} {e = e} (⊢-· ⊢₁ ⊢₂) with (progress ⊢₁) with (progress ⊢₂) with (p matches? e)
progress (⊢-· ⊢₁ ⊢₂) | step S₁ | step S₂ | M = step (step {!!} {!!} {!!} {!!} {!!})
progress (⊢-· ⊢₁ ⊢₂) | step S | skip x | M = {!!}
progress (⊢-· ⊢₁ ⊢₂) | step S | done x | M = {!!}
progress (⊢-· ⊢₁ ⊢₂) | skip x | _ | M = {!!}
progress (⊢-· ⊢₁ ⊢₂) | done x | _ | M = {!!}
progress (⊢-+ ⊢₁ ⊢₂) = {!!}
progress ⊢-# = {!!}
progress (⊢-φ x ⊢) = {!!}
progress (⊢-δ ⊢) = {!!}

step-preserve : ∀ {Γ e τ p a g l e′}
  → Γ ⊢ e ∶ τ
  → (p , a , g , l) ⊢ e ⇥ e′
  → Γ ⊢ e′ ∶ τ
step-preserve ⊢ (step x x₁ x₂ x₃ x₄) = {!!}
