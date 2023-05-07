module Mult

import Plus

public export

total

mult_comm_z : (x : Nat) -> mult x 0 = 0
mult_comm_z 0 = Refl
mult_comm_z (S k) = mult_comm_z k

mult_1_x_eq_x : (x : Nat) -> mult x 1 = plus x 0
mult_1_x_eq_x 0 = Refl
mult_1_x_eq_x (S k) = cong S (mult_1_x_eq_x k)

mult_comm_s : (k : Nat) -> (x : Nat) -> mult x (S k) = plus x (mult k x)
mult_comm_s 0 x = mult_1_x_eq_x x
mult_comm_s (S k) x = 
    let rec = sym (mult_comm_s (S k) x) in
    rewrite rec in Refl

mult_comm : (x : Nat) -> (y : Nat) -> x * y = y * x
mult_comm x 0 = mult_comm_z x
mult_comm x (S k) = mult_comm_s k x

mult_assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> (x * y) * z = x * (y * z)
mult_assoc x y 0 = 
    let a = mult_comm_z y in
    rewrite a in 
    let b = mult_comm_z (x * y) in
    rewrite b in 
    let c = mult_comm_z x in
    rewrite c in Refl
mult_assoc x y (S k) = 
    let step = mult_assoc x y (S k) in
    rewrite step in Refl

mult_distr : (x : Nat) -> (y : Nat) -> (z : Nat) -> x * (y * z) = (x * y) + (x * z)
mult_distr 0 y z = Refl
mult_distr (S k) y z = 
    let comm_all = sym (mult_comm_s k (y * z)) in
    rewrite comm_all in 
    let comm_sk = mult_comm (mult y z) (S k)  in
    rewrite comm_sk in 
    let distr = mult_distr (S k) y z in
    rewrite distr in Refl
