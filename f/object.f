Counter = Rec CC . {
    c : Ref Nat,
    get : CC -> Nat,
    inc : CC -> Unit,
    clone : CC -> CC
};

makeCounter = fix (lambda constr : Unit -> Counter .
  lambda _:Unit .
    fold [Counter] {
       c = ref 0,
       get = lambda this : Counter . 
               ! (unfold [Counter] this).c,
       inc = lambda this : Counter .
               let c = (unfold [Counter] this).c in
                 c := succ (!c),
       clone = lambda this : Counter .
                 let res = constr unit in
                   ( (unfold [Counter] res).c := !(unfold [Counter] this).c;
                     res )
    });

/* attempt #2 */
                 
ICounter = Rec CC . {
    get : Unit -> Nat,
    inc : Unit -> Unit,
    clone : Unit -> CC
};

RCounter = { c : Ref Nat };

privateCounter = fix ( lambda constr : RCounter -> ICounter .
                      lambda rep : RCounter .
                        fold [ICounter ] {
                          get = lambda _:Unit .
                                  !(rep.c),
                          inc = lambda _:Unit .
                                  rep.c := succ (!(rep.c)),
                          clone = lambda _:Unit .
                                    let res = constr { c = ref (!(rep.c)) } in
                                      res
                       } );

makeCounter = lambda _:Unit . privateCounter { c = ref 0 };

sendinc = lambda c:ICounter . (unfold [ICounter] c).inc unit;
sendget = lambda c:ICounter . (unfold [ICounter] c).get unit;
sendclone = lambda c:ICounter . (unfold [ICounter] c).clone unit;

c = makeCounter unit;

sendinc c;
sendinc c;
sendget c;

IBCounter = Rec BC . {
    get : Unit -> Nat,
    inc : Unit -> Unit,
    clone : Unit -> BC,
    reset : Unit -> Unit
};

RBCounter = {
    c : Ref Nat,
    bkp : Ref Nat
};

testf = lambda bc : IBCounter .
          sendinc bc;

makeBCounter = fix ( lambda const : RBCounter -> IBCounter .
                       lambda rep : RBCounter .
                         let super = unfold [ICounter] (privateCounter rep) in
                           fold [IBCounter] {
                             get = super.get,
                             inc = lambda _:Unit .
                                      ( rep.bkp := !(rep.c);
                                        super.inc unit ),
                             clone = super.clone, /* wrong */
                             reset = lambda _:Unit .
                                       rep.c := !(rep.bkp)
                           }
                       );


