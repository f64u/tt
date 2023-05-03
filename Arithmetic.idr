module Arithmetic

import Data.Vect
import Data.Fin

%default total

plusZeq : (n : Nat) -> n = n + Z
plusZeq Z = Refl
plusZeq (S k) = cong S (plusZeq k)

sPlusEqPlusS : (a, b : Nat) -> S (a + b) = a + (S b)
sPlusEqPlusS Z _ = Refl
sPlusEqPlusS (S k) j = cong S (sPlusEqPlusS k j)

commPlus : (a, b : Nat) -> a + b = b + a
commPlus Z j = plusZeq j
commPlus (S k) j = 
  let rec = sPlusEqPlusS j k in
  rewrite sym rec in cong S (commPlus k j)

assocPlus : (a, b, c : Nat) -> a + (b + c) = (a + b) + c
assocPlus Z b c = Refl
assocPlus (S k) b c = cong S (assocPlus k b c)

assocFlip : (a, b, c : Nat) -> a + (b + c) = b + (a + c)
assocFlip a b c =
  rewrite assocPlus a b c in
  rewrite cong (+ c) (commPlus a b) in 
  sym (assocPlus b a c)

timesZeqZ : (n : Nat) -> n * Z = Z
timesZeqZ Z = Refl
timesZeqZ (S k) = timesZeqZ k




main : IO ()
main = putStrLn "Hello, World"