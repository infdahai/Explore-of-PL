module agda_test.induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import agda_test.naturals using (ℕ; zero; suc; _+_; _*_; _∸_)

-- ‌1. ­Identity  : 0 + n ≡ n and n + 0 ≡ n .
-- 2. Associativity  : ( m + n ) + p ≡ m + ( n + p)
-- 3. Commutativity  : m + n ≡ n + m .
-- 4. Distribuivity  : ( m + n) * p ≡ ( m * p ) + ( n * p) .

_ : ( 3 + 4 ) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    ( 3 + 4 ) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + ( 4 + 5)
  ∎

+-assoc : ∀ ( m n p : ℕ ) → ( m + n ) + p ≡ m + ( n + p )
+-assoc zero n p =
  begin
    ( zero + n ) + p
  ≡⟨⟩
      n + p
  ≡⟨⟩
    zero + ( n + p )
  ∎
+-assoc ( suc m ) n p =
  begin
    (suc m + n ) + p
  ≡⟨⟩
    suc ( m + n ) + p
  ≡⟨⟩
    suc ( ( m + n ) + p )
  ≡⟨ cong suc (+-assoc m n p ) ⟩
    suc ( m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityᴿ : ∀ ( m : ℕ )  →  m + zero ≡ m
+-identityᴿ  zero =
    begin
      zero + zero
    ≡⟨⟩
      zero
    ∎
+-identityᴿ (suc m) =
      begin
        suc m + zero
      ≡⟨⟩
        suc (m + zero)
      ≡⟨ cong suc (+-identityᴿ m) ⟩
        suc m
      ∎

+-suc : ∀ ( m n : ℕ ) → m + suc n ≡ suc ( m + n )
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc ( zero + n )
  ∎
+-suc ( suc m )  n  =
  begin
    suc m + suc n
  ≡⟨⟩
    suc ( m + suc n )
  ≡⟨ cong suc (+-suc m n ) ⟩
    suc ( suc ( m + n ) )
  ≡⟨⟩
    suc ( suc m + n )
  ∎


+-comm : ∀ ( m n : ℕ ) →  m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityᴿ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m ( suc n ) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc ( m + n )
  ≡⟨ cong suc (+-comm m n ) ⟩
    suc n + m
  ∎
