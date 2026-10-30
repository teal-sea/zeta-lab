/-
Gabcke, Satz 2.1.1: the numbers `λ_n` in the Riemann-Siegel coefficients.

`λ_0 = 1` and `(n + 1) λ_{n+1} = Σ_{k=0}^{n} 2^{4k+1} |E_{2k+2}| λ_{n-k}`,
where `E_{2k}` are the Euler numbers from the secant recurrence. The seven
values are the ones printed on pages 19–20 of the 2015 PDF. This file does
not state the remainder bound.
-/

def binom (n k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k + 1 => if n < k + 1 then 0 else binom n k * (n - k) / (k + 1)

def walkEuler (base k : Nat) : List Int → Int
  | [] => 0
  | e :: rest => (binom base (2 * k) : Int) * e + walkEuler base (k + 1) rest

/-- `E_0, E_2, ..., E_{2n}`. -/
def eulerList : Nat → List Int
  | 0 => [1]
  | n + 1 =>
    let prev := eulerList n
    prev ++ [-walkEuler (2 * prev.length) 0 prev]

def euler2 (n : Nat) : Int :=
  (eulerList n).getLastD 0

def atIndex : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => atIndex xs i

/-- Sum `k = 0` to `k` of the Satz 2.1.1 term, with `n = prev.length - 1`. -/
def walkLam (prev : List Nat) : Nat → Nat
  | 0 =>
    let n := prev.length - 1
    2 ^ 1 * (euler2 1).natAbs * atIndex prev n
  | k + 1 =>
    let n := prev.length - 1
    2 ^ (4 * (k + 1) + 1) * (euler2 (k + 2)).natAbs * atIndex prev (n - (k + 1))
      + walkLam prev k

/-- `λ_0` through `λ_n`. -/
def lambdas : Nat → List Nat
  | 0 => [1]
  | n + 1 =>
    let prev := lambdas n
    prev ++ [walkLam prev n / (n + 1)]

def lambda (n : Nat) : Nat :=
  atIndex (lambdas n) n

theorem lambda_printed :
    lambda 0 = 1
    ∧ lambda 1 = 2
    ∧ lambda 2 = 2 * 41
    ∧ lambda 3 = 4 * 3 * 881
    ∧ lambda 4 = 2 * 3 * 7 * 68111
    ∧ lambda 5 = 4 * 3 * 47 * 499 * 4729
    ∧ lambda 6 = 4 * 3 * 409 * 193077047 := by
  decide

theorem lambda_divides :
    1 * lambda 1 = walkLam (lambdas 0) 0
    ∧ 2 * lambda 2 = walkLam (lambdas 1) 1
    ∧ 3 * lambda 3 = walkLam (lambdas 2) 2
    ∧ 4 * lambda 4 = walkLam (lambdas 3) 3
    ∧ 5 * lambda 5 = walkLam (lambdas 4) 4
    ∧ 6 * lambda 6 = walkLam (lambdas 5) 5
    ∧ 7 * lambda 7 = walkLam (lambdas 6) 6 := by
  decide

#print axioms lambda_printed
#print axioms lambda_divides
