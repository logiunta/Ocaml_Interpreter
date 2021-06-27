type ide = string;;
type exp = Eint of int | Ebool of bool | EString of string | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | Dictionary of collection | Select of exp * ide | Remove of ide * exp | 
	Add of ide * exp * exp | Clear of exp | ApplyOver of exp * exp 
 and collection = Empty | Pair of ide * exp* collection;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

type evT = Int of int | Bool of bool | String of string | Unbound | FunVal of evFun | 
           RecFunVal of ide * evFun | DictionaryVal of (ide * evT) list 
and evFun = ide * exp

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	"string" -> (match v with
		String(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

let rec rt_eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	EString s -> String s |
	IsZero a -> iszero (rt_eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (rt_eval a r) (rt_eval b r) |
	Prod(a, b) -> prod (rt_eval a r) (rt_eval b r) |
	Sum(a, b) -> sum (rt_eval a r) (rt_eval b r) |
	Diff(a, b) -> diff (rt_eval a r) (rt_eval b r) |
	Minus a -> minus (rt_eval a r) |
	And(a, b) -> et (rt_eval a r) (rt_eval b r) |
	Or(a, b) -> vel (rt_eval a r) (rt_eval b r) |
	Not a -> non (rt_eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (rt_eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (rt_eval b r) else (rt_eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> rt_eval e2 (bind r i (rt_eval e1 r)) |
	Fun(i, a) -> FunVal(i, a) |
    FunCall(f, eArg) -> 
		let fClosure = (rt_eval f r) in
			(match fClosure with
				FunVal(arg, fBody) -> 
					rt_eval fBody (bind r arg (rt_eval eArg r)) |
				RecFunVal(g, (arg, fBody)) -> 
					let aVal = (rt_eval eArg r) in
						let rEnv = (bind r g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								rt_eval fBody aEnv |
				_ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
        	(match funDef with
        		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody)))) in
                     			                rt_eval letBody r1 |
        		_ -> failwith("non functional def")) |
    Dictionary(c) -> DictionaryVal(rt_evalColl c r) |
	Select(e,i) -> (match rt_eval e r  with
    			    DictionaryVal(c) -> pick c i |
    			    _ -> failwith("Is not a Dictionary") ) |
	Clear(e) ->  (match rt_eval e r with
				 DictionaryVal(c) -> DictionaryVal([])  |
				 _ -> failwith("Is not a Dictionary")) |
	Add(i,e1,e2) -> (match rt_eval e2 r with
					DictionaryVal(c) -> if (alreadyExists c i) then failwith("Id already exists")
										else  DictionaryVal((i, rt_eval e1 r) :: c)|
					_ -> failwith ("Is not a Dictionary")) |
	Remove(i,e1) -> (match rt_eval e1 r with
					DictionaryVal(c) -> DictionaryVal(delete c i) |
					_ -> failwith ("Is not a Dictionary")) |
	ApplyOver(f,e1) -> (match e1 with
						Dictionary(c) -> DictionaryVal(map c f r )|
						_ -> failwith("Is not a Dictionary"))



(*rt_evalColl prende una collezione nel suo ambiente e la restituisce valutandone i valori *)
and rt_evalColl (c : collection) (r : 't env) : (ide * evT) list = match c with 
	Empty -> [] |
	Pair(i,e,c1) -> (i, rt_eval e r)::rt_evalColl c1 r 
and pick (l : (ide * evT) list) (id: ide) : evT = match l with 
	[] -> failwith ("Not found") |
	(id1,e1) :: ls-> if (id = id1) then e1 else (pick ls id) 
and alreadyExists (l : (ide * evT) list) (id: ide) : bool = match l with
	[] -> false |
	(id1,_) :: ls -> if (id1 = id) then true else alreadyExists ls id
and delete (l : (ide * evT) list) (id: ide) : (ide * evT) list = match l with
	[] -> failwith ("Not found") |
	(id1,e1) :: ls -> if (id=id1) then ls else (id1,e1) :: (delete ls id)
(*la map restituisce <un identificatore, la valutazione della chiamata di f passandogli il valore come espressione> concatenandola alla ricorsione di map su tutta la collezione*)
and map (c : collection) (f : exp) (r : 't env) : (ide * evT) list = match c with
	Empty -> [] |
	Pair (i,e,c1) -> (i, rt_eval (FunCall(f,e)) r) :: map c1 f r ;;




