succ 0;
CList E = All R . (E -> R -> R) -> R -> R;

nil = lambda E . ((lambda R . lambda f:E -> R -> R . lambda r:R . r) as CList E);
cons = lambda E . lambda x:E . 
       lambda l:CList E . 
         (lambda R . lambda f : E -> R -> R. lambda r:R . 
               f x (l [R] f r)) as CList E;

l0 = nil [Nat];
l1 = cons [Nat] 1 l0;
l321 = cons [Nat] 3 (cons [Nat] 2 l1);

/* digressio*/

plus = fix (lambda p : Nat -> Nat -> Nat . lambda m:Nat . lambda n : Nat . if iszero m then n else succ (p (pred m) n));

plus 3 4;

/* back to lists */

l321 [Nat] plus 0;

isEmpty = lambda E . lambda l:CList E . l [Bool] (lambda x:E . lambda r:Bool . false) true;

"isEmpty l1";
isEmpty [Nat] l1;
"isEmpty l0";
isEmpty [Nat] l0;

/* head = lambda E . lambda l:CList E . l [E] (lambda x:E . lambda r:E . x)  */

length = lambda E . lambda l : CList E . l [Nat] (lambda x:E . lambda r:Nat . succ r) 0;

"length l321";
length [Nat] l321;

l8701 = cons [Nat] 8 (cons [Nat] 7 (cons [Nat] 0 (cons [Nat] 1 l0)));
"length l8701";
length [Nat] l8701;

Counter = {Some R ,  {get: R -> Nat , inc : R -> R}};

mycount = {*Nat , { get = lambda r:Nat . r, inc = lambda r : Nat . succ r } } as Counter;
