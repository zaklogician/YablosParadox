{-# OPTIONS --no-positivity-check #-}

module Yablo where

----------------------------------------------------------------------------
-- Some useful misc. properties of the ordering relations ≤ and <

open import Data.Nat
open import Data.Empty

<-reduce : ∀ {k n} → suc n < k → n < k
<-reduce (s≤s (s≤s z≤n)) = s≤s z≤n
<-reduce (s≤s (s≤s (s≤s sn<k))) = s≤s (<-reduce (s≤s (s≤s sn<k)))

≤-refl : ∀ n → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

----------------------------------------------------------------------------
-- The family of Yablo sentences (not strictly positive)

data Yablo (n : ℕ) : Set where
  yy : (∀ k → n < k → Yablo k → ⊥) → Yablo n

----------------------------------------------------------------------------
-- Proof of the paradox


-- Step 1: If a Yablo sentence is true, then all subsequent ones are true
step1 : ∀ n → Yablo n → Yablo (suc n)
step1 n (yy inner0) = yy inner1 where
  inner1 : (k : ℕ) → suc n < k → Yablo k → ⊥
  inner1 k sn<k yk = inner0 k (<-reduce sn<k) yk

-- Step 2: But a Yablo sentence asserts that all subsequent ones are false
step2 : ∀ n → Yablo n → Yablo (suc n) → ⊥
step2 n (yy inner0) = inner0 (suc n) (s≤s (≤-refl n)) 

-- Step 3: Therefore, all Yablo sentences are false
step3 : ∀ n → Yablo n → ⊥
step3 n yn = (step2 n yn) (step1 n yn)

-- Step 4: If all Yablo sentences are false, then all Yablo sentences
--         subsequent to the first are false, so Yablo 0 is true.
step4 : Yablo 0
step4 = yy inner0 where
  inner0 : (k : ℕ) → 0 < k → Yablo k → ⊥
  inner0 k 0<k yk = step3 k yk

-- Conclusion: Yablo 0 is both true and false.
paradox : ⊥
paradox = step3 0 step4
