

Module boolean.
Inductive bool: Type :=
  |true
  |false.
  
(*punto 1*)
Definition bnand (b1:bool)(b2:bool) : bool :=
  match b1,b2 with
  | true, true => false
  | _, _ => true
  end.


(*Ejemplos (00, 01, 10, 11)*)

(*00*)
Example testbnand00: (bnand false false) = true.
Proof. simpl. reflexivity. Qed.

(*01*)
Example testbnand01: (bnand false true) = true.
Proof. simpl. reflexivity. Qed.

(*10*)
Example testbnand10: (bnand true false) = true.
Proof. simpl. reflexivity. Qed.

(*11*)
Example testbnand11: (bnand true true) = false.
Proof. simpl. reflexivity. Qed.


(*punto 2*)

(*negacion*)
Definition neg (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(*conjuncion*)
Definition and (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


(*neg y and*)
Definition Bnand (b1:bool)(b2:bool) : bool :=
  match (and b1 b2) with
  | true => false
  | false => true
  end.


Compute bnand true true.
Compute Bnand true true.

Example testBnand01: (Bnand true true) = false.
Proof. simpl. reflexivity. Qed.
End boolean.

(*punto3*)
Module Direct.
Inductive direccion : Type :=
  |O.

(*punto 4*)
Module Natural.
Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred(n :nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
  
End Natural.




(*Punto 5*)

Definition subtwo (n: nat) : nat := 
  match n with
  |0 => 0
  |1 => 0
  |_ => (pred(n)-1)
  end.

Compute subtwo 0.

(* Definir una funci´on que reciba dos funciones y retorne la composici´on de
ambas. (Tener en cuenta que el valor de retorno es una funci´on)*)

(*punto 6*)
Definition returnDosFunciones (f: nat -> nat ) ( g: nat -> nat ) : nat -> nat  :=
fun(x: nat) => f(g(x)).

(*punto 7*)
Definition suma (a:nat)(b:nat) : nat := (a+b).

(*punto 8*)
Definition sumprod (a:nat)(b:nat) : (nat*nat) := ((a+b),(a*b)).
Compute sumprod 5 2.

Compute Nat.leb (100)(1).


(*punto 9*)
Definition pares (g: nat->nat)(f:(nat->nat)->nat)(a: nat)(b:nat) : (g(b)*f(b*a)) :=

(*punto10*)
Definition par (n: nat): bool :=
  match n with
    |1 => true
    |_ => 1*+par(n-2) 
  end.


 
 
 (*punto12 *)
Definition parejafunc (a: nat)( b: nat)(f: nat -> nat): nat->nat := 
  if (Nat.leb a b) then fun (x: nat) => f(a-b) 
  else fun (x: nat) => f(b+1).
  
  
 
