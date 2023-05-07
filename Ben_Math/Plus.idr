module Plus

public export

total

plus_comm_z : (y : Nat) -> y = plus y 0
plus_comm_z 0 = Refl
plus_comm_z (S k) = let i = plus_comm_z k in
    rewrite sym i in
    Refl

plus_comm_s : (k : Nat) -> (y : Nat) -> S (plus k y) = plus y (S k)
plus_comm_s k 0 = cong S (sym (plus_comm_z k))
plus_comm_s k (S j) = let rec = plus_comm_s k (S j) in 
    rewrite rec in Refl

plus_comm : (x : Nat) -> (y : Nat) -> x + y = y + x
plus_comm 0 y = plus_comm_z y
plus_comm (S k) y = plus_comm_s k y

assoc_base : (x : Nat) -> (y : Nat) -> x + (y + 0) = (x + y) + 0
assoc_base x y = 
    let i = sym (plus_comm_z y) in rewrite i in 
    let j = sym (plus_comm_z (plus x y)) in rewrite j in Refl

plus_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> x + (y + z) = (x + y) + z
plus_assoc x y 0 = assoc_base x y
plus_assoc x y (S k) = 
    let rec = sym (plus_assoc k y x) in 
    let a = sym (plus_comm_s k y) in 
    rewrite a in 
    let b = sym (plus_comm_s (plus k y) x) in
    rewrite b in 
    rewrite rec in
    let c = (plus_comm (plus x y) (S k))  in
    rewrite c in 
    let d = plus_comm x y in
    rewrite d in Refl
