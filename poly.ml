open Expr;;
(* Sum type to encode efficiently polynomial expressions *)
type pExp =
  | Term of int*int (*
      First int is the constant
      Second int is the power of x 
      10  -> Term(10,0)
      2x -> Term(2,1)
      3x^20 -> Term(3, 20)
    *)
  | Plus of pExp list
  (*
    List of terms added
    Plus([Term(2,1); Term(1,0)])
  *)
  | Times of pExp list (* List of terms multiplied *)


(*
  Function to traslate betwen AST expressions
  to pExp expressions
*)

let rec multConv (pE: pExp) (v: int) (l: pExp list): pExp list =
  if(v = 0) then l
  else 
  match l with
  |[] -> multConv pE (v-1) [pE]@[]
  |h::t -> multConv pE (v-1) (h::(t@[pE]))

and from_expr (_e: Expr.expr) : pExp =
    match _e with
    |Num(v) -> Term(v, 0)
    |Var(x) -> Term(1, 1)
    |Add(e1, e2) -> Plus([(from_expr e1); (from_expr e2)])
    |Sub(e1, e2) -> Plus([(from_expr e1); Times([Term(-1, 0); (from_expr e2)])])
    |Mul(e1, e2) -> 
      begin match e1 with
      |Num(v) ->
        begin match e2 with
        |Var(x2) -> Term(v, 1)
        |Num(v2) -> Term(v * v2, 0)
        |_ -> Times([(from_expr e1); (from_expr e2)])
        end
      |Var(x) ->
        begin match e2 with
        |Num(v2) -> Term(v2, 1)
        |Var(x2) -> Term(1, 2)
        |_ -> Times([(from_expr e1); (from_expr e2)])
        end
      |_ -> Times([(from_expr e1); (from_expr e2)])
      end
    |Pow(e, v) -> let pE = from_expr e in 
      let mult = (multConv pE v []) in
      Times(mult)
    |Pos(e) -> from_expr e
    |Neg(e) -> Times([Term(-1, 0); (from_expr e)])
     (* TODO *)


(* 
  Compute degree of a polynomial expression.

  Hint 1: Degree of Term(n,m) is m
  Hint 2: Degree of Plus[...] is the max of the degree of args
  Hint 3: Degree of Times[...] is the sum of the degree of args 
*)
and degree (_e:pExp): int = 
  match _e with
  |Term(c, p) -> p
  |Plus(pL) -> findMax (List.map degree pL)
  |Times(pL) -> List.fold_left (fun sum x -> sum + x) 0 (List.map degree pL)

and findMax (degList: int list): int =
  match degList with
  |h1::h2::t -> max h1 (findMax (h2::t))
  |h::t -> h

(* 
  Comparison function useful for sorting of Plus[..] args 
  to "normalize them". This way, terms that need to be reduced
  show up one after another.
  *)
and compare (e1: pExp) (e2: pExp) : int =
  if(degree e1 > degree e2) then -1
  else if(degree e1 < degree e2) then 1
  else 0

(* Print a pExpr nicely 
  Term(3,0) -> 3
  Term(5,1) -> 5x 
  Term(4,2) -> 4x^2
  Plus... -> () + () 
  Times ... -> ()() .. ()

  Hint 1: Print () around elements that are not Term() 
  Hint 2: Recurse on the elements of Plus[..] or Times[..]
*)
and print_pExp (_e: pExp): unit =
  (* TODO *)
  match _e with
  |Term(c, p) ->
    if(c < 0) then print_string "(-"
    else ();
    if(not(abs c = 1 && p != 0)) then print_int (abs c)
    else ();
    if(p != 0 && c != 0) then print_string "x"
    else ();
    if(p != 0 && p != 1 && c != 0) then (print_string "^"; print_int p)
    else ();
    if(c < 0) then print_string ")"
    else ();
  |Plus(pL) ->
    begin match pL with
    |[] -> print_int 0
    |_ ->
      print_string "(";
      plusPrint pL;
      print_string ")";
    end
  |Times(pL) ->
    begin match pL with
      |[] -> print_int 0
      |_ ->
        print_string "(";
        timesPrint pL;
        print_string ")";
    end

and plusPrint (pL: pExp list): unit =
  match pL with
  |[] -> ()
  |h1::h2::t -> print_pExp h1; print_string "+"; plusPrint (h2::t);
  |h::t -> print_pExp h

and timesPrint (pL: pExp list): unit =
  match pL with
  |[] -> ()
  |h1::h2::t -> print_pExp h1; print_string "*"; timesPrint (h2::t);
  |h::t -> print_pExp h; timesPrint t;

(* 
  Function to simplify (one pass) pExpr

  n1 x^m1 * n2 x^m2 -> n1*n2 x^(m1+m2)
  Term(n1,m1)*Term(n2,m2) -> Term(n1*n2,m1+m2)

  Hint 1: Keep terms in Plus[...] sorted
  Hint 2: flatten plus, i.e. Plus[ Plus[..], ..] => Plus[..]
  Hint 3: flatten times, i.e. times of times is times
  Hint 4: Accumulate terms. Term(n1,m)+Term(n2,m) => Term(n1+n2,m)
          Term(n1, m1)*Term(n2,m2) => Term(n1*n2, m1+m2)
  Hint 5: Use distributivity, i.e. Times[Plus[..],] => Plus[Times[..],]
    i.e. Times[Plus[Term(1,1); Term(2,2)]; Term(3,3)] 
      => Plus[Times[Term(1,1); Term(3,3)]; Times[Term(2,2); Term(3,3)]]
      => Plus[Term(2,3); Term(6,5)]
  Hint 6: Find other situations that can arise
*)
and simplify1 (e:pExp): pExp =
  begin match e with
  |Term(c, p) -> Term(c, p) 
  |Plus(pL) ->
    let plusExist = findPlus pL 0 in
    if(plusExist >= 0) then let innerPlus = (List.nth pL plusExist) in
      begin match innerPlus with
      |Plus(pList) -> Plus(flattenPlus pL pList 0 plusExist)
      end
    else let timesExist = findTimes pL 0 in
    if(timesExist >= 0) then let newExp = simplify1 (List.nth pL timesExist) in
    Plus(replaceTimes newExp pL 0 timesExist)
    else Plus(addTerms (List.sort compare pL))
  |Times(pL) ->
    let timesExist = findTimes pL 0 in
    if(timesExist >= 0) then let innerTimes = (List.nth pL timesExist) in
      begin match innerTimes with
      |Times(pList) -> Times(flattenTimes pL pList 0 timesExist)
      end
    else (simplifyTimes pL)
  end

and findPlus (pL: pExp list) (index: int): int =
  match pL with
  |[] -> -1
  |h::t -> 
    match h with
    |Plus(pList) -> index
    |_ -> findPlus t (index + 1)


and findTimes (pL: pExp list) (index: int): int =
  match pL with
  |[] -> -1
  |h::t -> 
    match h with
    |Times(pList) -> index
    |_ -> findTimes t (index + 1)

and replaceTimes (newExp: pExp) (pL: pExp list) (index: int) (n: int): pExp list =
  match pL with
  |[] -> pL
  |h::t -> 
    if(index = n) then newExp::t
    else h::(replaceTimes newExp t (index + 1) n)


and flattenPlus (pL: pExp list) (innerList: pExp list) (index: int) (n: int): pExp list =
  match pL with
  |[] -> innerList
  |h::t -> 
    if(index = n) then flattenPlus t innerList (index + 1) n
    else flattenPlus t (innerList@[h]) (index + 1) n

and flattenTimes (pL: pExp list) (innerList: pExp list) (index: int) (n: int): pExp list =
  begin match pL with
  |[] -> innerList
  |h::t -> 
    if(index = n) then flattenTimes t innerList (index + 1) n
    else flattenTimes t (innerList@[h]) (index + 1) n
  end

and addTerms (pL: pExp list): pExp list =
  begin match pL with
  |[] -> pL
  |h1::h2::t ->
    begin match h1 with
    |Term(c1, p1) ->
      begin match h2 with
      |Term(c2, p2) -> 
        if(p1 = p2 && (c1 + c2) = 0) then (addTerms t)
        else if(p1 = p2 || c2 = 0) then (Term(c1 + c2, p1))::(addTerms t)
        else if(c1 = 0) then (Term(c1 + c2, p2))::(addTerms t)
        else h1::(addTerms (h2::t))
      end
    end
  |h::t -> [h]
  end

and simplifyTimes (pL: pExp list): pExp =
  begin match pL with
  |[] -> Times([])
  |h1::h2::t -> 
    begin match h1 with
    |Plus(pList) -> Plus(plusDistribute pList (h2::t))
    |Term(c, v) ->
      begin match h2 with
      |Plus(pList) ->
        let plusExist = findPlus pList 0 in
        if(plusExist >= 0) then let innerPlus = (List.nth pList plusExist) in
          begin match innerPlus with
          |Plus(pList2) ->
            let res = (Plus(termDistribute h1 (flattenPlus pList pList2 0 plusExist))) in
            begin match t with
            |[] -> res
            |_ -> Times(res::t)
            end
          end
        else 
          let res = (Plus(termDistribute h1 pList)) in
          begin match t with
            |[] -> res
            |_ -> Times(res::t)
          end
      |Term(c2, v2) ->
        let res = (Term(c * c2, v + v2)) in
        begin match t with
        |[] -> res
        |_ -> Times(res::t)
        end
      end
    end
  end

and plusDistribute (pList: pExp list) (t: pExp list): pExp list =
  begin match pList with
  |[] -> []
  |h1::t1 -> 
      (Times(h1::t))::(plusDistribute t1 t)
  end

and termDistribute (trm: pExp) (pList: pExp list): pExp list =
  begin match pList with
  |[] -> []
  |h::t -> 
      (Times([trm;h]))::(termDistribute trm t) 
  end
(* 
  Compute if two pExp are the same 
  Make sure this code works before you work on simplify1  
*)
and equal_pExp (_e1: pExp) (_e2: pExp) :bool =
  begin match _e1 with
  |Term(c1, p1) ->
    begin match _e2 with
    |Term(c2, p2) -> 
      if(c1 != c2) then false
      else if(p1 != p2) then false
      else true
    |_ -> false
    end
  |Plus(pL1) ->
    begin match _e2 with
    |Plus(pL2) -> (listMatch pL1 pL2)
    |_ -> false
    end
  |Times(pL1) ->
    begin match _e2 with
    |Times(pL2) -> (listMatch pL1 pL2)
    |_ -> false
    end
  end

and listMatch (pL1: pExp list) (pL2: pExp list): bool =
  begin match pL1 with
  |[] ->
    begin match pL2 with
    |[] -> true
    |_ -> false
    end
  |h1::t1 ->
    begin match pL2 with
    |[] -> false
    |h2::t2 -> 
      if(equal_pExp h1 h2) then (listMatch t1 t2)
      else false
    end
  end
(* Fixed point version of simplify1 
  i.e. Apply simplify1 until no 
  progress is made
*)    
and simplify (e:pExp): pExp =
    let rE = simplify1(e) in
      if (equal_pExp e rE) then
        e
      else  
        simplify(rE)
      (*print_pExp rE;
      print_endline "end";
      rE;*)




