(* batteria di test per la prima implementazione con scoping statico *)


(* creazione di un ambiente vuoto *)
let env0 = emptyenv Unbound;;

(* creazione di un dizionario vuoto *)
let myDictEmpty = Dictionary(Empty);;
eval myDictEmpty env0;;

(* creazione di un dizionario riempito con 4 valori *)
let myDict1 = Dictionary(Pair("due",Eint(2),Pair("quattro",Eint(4),Pair("cinque",Eint(5),Pair("sei",Eint(6),Empty)))));;
eval myDict1 env0;;

(* creazione del dizionario my_dict con 2 valori *)
let my_dict = Dictionary(Pair("name",Estring("Giovanni"),Pair("matricola",Eint(123456),Empty)));;
eval my_dict env0;;

(* accedere ad un elemento del dizionario my_dict *)
let accessmy_dict = Select(my_dict,"matricola");;
eval accessmy_dict env0;;

(* accedere ad un elemento del dizionario myDict1 *)
let accessDict = Select(myDict1,"sei");;
eval accessDict env0;;

(* accedere ad un elemento del dizionario myDictEmpty che non è presente *)
let accessDictEmpty= Select(myDictEmpty,"sei");;
eval accessDictEmpty env0;;

(*aggiunta in testa di un nuovo valore nel dizionario myDict1 *)
let addDict = Add("otto",Eint(8),myDict1);;
eval addDict env0;;

(* accedere al nuovo valore aggiunto al dizionario myDict1 *)
let accessNewelement = Select(Add("otto",Eint(8),myDict1),"otto");;
eval accessNewelement env0;;

(* liberare un dizionario rendedolo vuoto *)
let deleteAll = Clear(myDict1);;
eval deleteAll env0;;

(* eliminare un elemento dal dizionario my_dict attraverso il suo indentificatore *)
let delete = Remove("name",my_dict);;
eval delete env0;;

(* funzione che incrementa di 1 il valore di tutti gli elementi presenti in myDict1 *)
let funzione = ApplyOver(Fun("x",Sum(Den("x"),Eint(1))),myDict1);;
eval funzione env0;;




