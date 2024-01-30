open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; [_])
open Eq.≡-Reasoning

Id : Set
Id = String

Filter : Set

data Pat : Set
data Act : Set
data Gas : Set

infix  5 ƛ_⇒_
infixl 7 _·_
infixl 7 _`+_
infix  9 #_
infix  9 `_

data Term : Set where
  `_    : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_   : Term → Term → Term
  #_    : ℕ → Term
  _`+_  : Term → Term → Term
  Φ_⇐_ : Filter → Term → Term
  φ_←_ : Act × Gas → Term → Term

data Value : Term → Set where
  V-ƛ : ∀ {x N}
    → Value (ƛ x ⇒ N)

  V-# : ∀ {n}
    → Value (# n)

Value? : ∀ (L : Term) → Dec (Value L)
Value? (` x) = no λ ()
Value? (ƛ x ⇒ L) = yes V-ƛ
Value? (L · M) = no λ ()
Value? (Φ x ⇐ L) = no λ ()
Value? (φ x ← L) = no λ ()
Value? (# n) = yes V-#
Value? (L `+ M) = no λ ()

data Pat where
  `_  : Id → Pat
  `e    : Pat
  `v    : Pat
  ƛ_⇒_ : Id → Term → Pat
  _·_   : Pat → Pat → Pat
  #_    : ℕ → Pat
  _`+_  : Pat → Pat → Pat

infix 1 _matches_

data _matches_ : Pat → Term → Set where
  PM-`e : ∀ {L}
    → `e matches L

  PM-`v : ∀ {V}
    → Value V
    → `v matches V

  PM-· : ∀ {p₁ p₂ e₁ e₂}
    → p₁ matches e₁
    → p₂ matches e₂
    → p₁ · p₂ matches e₁ · e₂

  PM-# : ∀ {n}
    → # n matches # n

  PM-+ : ∀ {p₁ p₂ e₁ e₂}
    → p₁ matches e₁
    → p₂ matches e₂
    → p₁ `+ p₂ matches e₁ `+ e₂

_matches?_ : ∀ (P : Pat) (L : Term) → Dec (P matches L)
(` _) matches? _ = no λ ()
`e matches? L = yes PM-`e
`v matches? L with Value? L
... | yes ValueL = yes (PM-`v ValueL)
... | no  ¬ValueL = no λ { (PM-`v ValueL) → ¬ValueL ValueL }

(ƛ _ ⇒ _) matches? _ = no λ ()

(Pₗ · Pᵣ) matches? (Lₗ · Lᵣ) with (Pₗ matches? Lₗ) ×-dec (Pᵣ matches? Lᵣ)
... | yes (PLₗ , PLᵣ) = yes (PM-· PLₗ PLᵣ)
... | no  ¬PLₗᵣ = no λ { (PM-· PLₗ PLᵣ) → ¬PLₗᵣ (PLₗ , PLᵣ) }
(_ · _) matches? (` _) = no λ ()
(_ · _) matches? (ƛ _ ⇒ _) = no λ ()
(_ · _) matches? (# _) = no λ ()
(_ · _) matches? (_ `+ _) = no λ ()
(_ · _) matches? (Φ _ ⇐ L) = no λ ()
(_ · _) matches? (φ _ ← _) = no λ ()

(# P) matches? (# L) with P Data.Nat.≟ L
... | yes refl = yes PM-#
... | no  P≢P  = no λ { PM-# → P≢P refl }
(# _) matches? (` _) = no λ ()
(# _) matches? (ƛ _ ⇒ _) = no λ ()
(# _) matches? (_ · _) = no λ ()
(# _) matches? (_ `+ _) = no λ ()
(# _) matches? (Φ _ ⇐ _) = no λ ()
(# _) matches? (φ _ ← _) = no λ ()

(Pₗ `+ Pᵣ) matches? (Lₗ `+ Lᵣ) with (Pₗ matches? Lₗ) ×-dec (Pᵣ matches? Lᵣ)
... | yes (PLₗ , PLᵣ) = yes (PM-+ PLₗ PLᵣ)
... | no  ¬PLₗᵣ       = no λ { (PM-+ PLₗ PLᵣ) → ¬PLₗᵣ (PLₗ , PLᵣ) }
(_ `+ _) matches? (` _) = no λ ()
(_ `+ _) matches? (ƛ _ ⇒ _) = no λ ()
(_ `+ _) matches? (_ · _) = no λ ()
(_ `+ _) matches? (# _) = no λ ()
(_ `+ _) matches? (Φ _ ⇐ _) = no λ ()
(_ `+ _) matches? (φ _ ← _) = no λ ()

_ : (`v `+ `v matches # 1 `+ # 2)
_ = PM-+ (PM-`v V-#) (PM-`v V-#)

_ : (`e `+ `e matches ((ƛ "x" ⇒ ` "x") · # 3) `+ (# 1 `+ # 2))
_ = PM-+ PM-`e PM-`e

data Act where
  stop : Act
  skip : Act

data Gas where
  one : Gas
  all : Gas

Filter = Pat × Act × Gas

infix 9 _[_:=_]
infix 9 _[_:=_]ᶠ

patternize : Term → Pat
patternize (` x) = ` x
patternize (ƛ x ⇒ N) = ƛ x ⇒ N
patternize (L · M) = patternize L · patternize M
patternize (# n) = # n
patternize (L `+ M) = patternize L `+ patternize M
patternize (Φ F ⇐ L) = patternize L
patternize (φ AG ← L) = patternize L

_[_:=_]ᶠ : Pat → Id → Term → Pat
_[_:=_]  : Term → Id → Term → Term

(` x) [ y := V ]ᶠ with x ≟ y
... | yes _ = patternize V
... | no  _ = ` x
`e [ y := V ]ᶠ = `e
`v [ y := V ]ᶠ = `v
(ƛ x ⇒ N) [ y := V ]ᶠ = ƛ x ⇒ (N [ y := V ])
(Pₗ · Pᵣ) [ y := V ]ᶠ = Pₗ [ y := V ]ᶠ · Pᵣ [ y := V ]ᶠ
(# n) [ y := V ]ᶠ = # n
(Pₗ `+ Pᵣ) [ y := V ]ᶠ = Pₗ [ y := V ]ᶠ `+ Pᵣ [ y := V ]ᶠ

(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
(# n) [ y := V ] = # n
(L `+ M) [ y := V ] = L [ y := V ] `+ M [ y := V ]
(Φ (F , A,G) ⇐ N) [ y := V ] = Φ (F [ y := V ]ᶠ , A,G) ⇐ (N [ y := V ])
(φ A,G ← N) [ y := V ] = φ A,G ← (N [ y := V ])

strip : Term → Term
strip (` x) = ` x
strip (ƛ x ⇒ L) = ƛ x ⇒ L
strip (L · M) = strip L · strip M
strip (# x) = # x
strip (L `+ M) = strip L `+ strip M
strip (Φ x ⇐ L) = L
strip (φ x ← L) = L

instr₀ : Filter → Term → Term
instr₀ (F , A,G) L with F matches? (strip L)
... | no  _ = L
... | yes _ with Value? (strip L)
... | yes _ = L
... | no  _ = φ A,G ← L

instr : Filter → Term → Term
instr F (` x) = (` x)
instr F (ƛ x ⇒ L) = (ƛ x ⇒ L)
instr F (L · M) = instr₀ F ((instr F L) · (instr F M))
instr F (# x) = (# x)
instr F (L `+ M) = instr₀ F ((instr F L) `+ (instr F M))
instr F (Φ x ⇐ L) = instr F L
instr F (φ x ← L) = instr F L

data Eval-Context : Set where
  ∘    : Eval-Context
  _·ₗ_ : Eval-Context → Term → Eval-Context
  _·ᵣ_ : Term → Eval-Context → Eval-Context

infix 1 _＝_⟨_⟩

data _＝_⟨_⟩ : Term → Eval-Context → Term → Set where
  DC-∘ : ∀ {e} → e ＝ ∘ ⟨ e ⟩

  DC-·ₗ : ∀ {e₁ e₂ e₁′ ε}
    → e₁ ＝ ε ⟨ e₁′ ⟩
    → (e₁ · e₂) ＝ (ε ·ₗ e₂) ⟨ e₁′ ⟩

  DC-·ᵣ : ∀ {e₁ e₂ e₂′ ε}
    → Value e₁
    → e₂ ＝ ε ⟨ e₂′ ⟩
    → (e₁ · e₂) ＝ (e₁ ·ᵣ ε) ⟨ e₂′ ⟩

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·ₗ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M

  ξ-·ᵣ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-Φ : ∀ {F L L′}
    → L —→ L′
    → Φ F ⇐ L —→ Φ F ⇐ L′

  β-Φ : ∀ {F V}
    → Value V
    → Φ F ⇐ V —→ V

  ξ-φ : ∀ {A,G L L′}
    → L —→ L′
    → (φ A,G ← L) —→ L′

  β-φ : ∀ {A,G V}
    → Value V
    → (φ A,G ← V) —→ V

infix 1 _∼_⟨_⟩


data _~_⟨_⟩ : Pat → Eval-Context → Term → Set where
  CM-∘ : ∀ {P e}
    → P matches e
    → P ~ ∘ ⟨ e ⟩

  CM-·ₗ : ∀ {P ε e₁ e₂}
    → P ~ ε ⟨ e₁ ⟩
    → P ~ (ε ·ₗ e₂) ⟨ e₁ ⟩

  CM-·ᵣ : ∀ {P ε e₁ e₂}
    → P ~ ε ⟨ e₂ ⟩
    → P ~ (e₁ ·ᵣ ε) ⟨ e₂ ⟩

data _→→_ : Term → Term → Set where
  tran : ∀ {L L′}
    → L —→ L′
    → L →→ L′
    

data _↦_ : Term → Term → Set where
  step : ∀ {e e₀ e₀′ ε e′}
    → e ＝ ε ⟨ e₀ ⟩
    → e₀ —→ e₀′
    → e′ ＝ ε ⟨ e₀′ ⟩
    → e ↦ e′


data Type : Set where
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context