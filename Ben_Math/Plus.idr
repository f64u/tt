module Plus

%default total


public export
suc_eq_plus_one : (x : Nat) -> (S x) = x + 1
suc_eq_plus_one 0 = Refl
suc_eq_plus_one (S k) = rewrite suc_eq_plus_one k in Refl

public export
plus_comm : (x : Nat) -> (y : Nat) -> x + y = y + x

public export
plus_comm_z : (y : Nat) -> y = plus y 0
plus_comm_z 0 = Refl
plus_comm_z (S k) = let i = plus_comm_z k in
    rewrite sym i in
    Refl

public export
plus_comm_s : (k : Nat) -> (y : Nat) -> S (plus k y) = plus y (S k)
plus_comm_s k 0 = cong S (sym (plus_comm_z k))
plus_comm_s k (S j) = 
    let rec1 = sym (plus_comm_s k j) in
    let rec2 = sym (plus_comm_s j k) in
    rewrite rec1 in rewrite rec2 in 
    cong S (cong S (plus_comm j k))

plus_comm 0 y = plus_comm_z y
plus_comm (S k) y = plus_comm_s k y

public export
assoc_base : (x : Nat) -> (y : Nat) -> x + (y + 0) = (x + y) + 0
assoc_base x y = 
    let i = sym (plus_comm_z y) in rewrite i in 
    let j = sym (plus_comm_z (plus x y)) in rewrite j in Refl

public export
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
