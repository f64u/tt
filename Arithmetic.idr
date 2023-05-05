module Arithmetic

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

timesSeqPlusTimes : (a, b : Nat) -> a + (a * b) = a * (S b)
timesSeqPlusTimes Z b = Refl
timesSeqPlusTimes (S k) b = 
  rewrite cong S (assocFlip k b (k * b)) in
  cong (S . (b +)) (timesSeqPlusTimes k b)

commTimes : (a, b : Nat) -> a * b = b * a
commTimes Z b =
  rewrite timesZeqZ b in
  Refl
commTimes (S k) b = 
  rewrite cong (b +) (commTimes k b) in
  timesSeqPlusTimes b k

distrPlusTimes : (a, b, c : Nat) -> (a + b) * c = a * c + b * c
distrPlusTimes Z b c = Refl
distrPlusTimes (S k) b c = 
  rewrite cong (c +) (distrPlusTimes k b c) in
  assocPlus c (k * c) (b * c)

distrTimesPlus : (a, b, c : Nat) -> a * (b + c) = a * b + a * c
distrTimesPlus a b c =
  rewrite commTimes a (b + c) in
  rewrite distrPlusTimes b c a in
  rewrite cong (+ (c * a)) (commTimes b a) in
  cong ((a * b) +) (commTimes c a) 


assocTimes : (a, b, c : Nat) -> a * (b * c) = (a * b) * c
assocTimes Z b c = Refl
assocTimes (S k) b c = 
  rewrite cong ((b * c) +) (assocTimes k b c) in
  sym (distrPlusTimes b (k * b) c)
