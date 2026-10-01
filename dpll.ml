open List

(** Ce fichier contient les fonctions à compléter. *)

(** Fonctions utilitaires. *)

(** filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien y ajouter.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(** Voici une proposition de types pour une implémentation simple.
    Vous pouvez éventuellement changer les types dans un deuxième temps. *)
type literal = int
type clause = literal list
type cnf = clause list
type interpretation = int list
type resultat = Sat of interpretation | Unsat

(** Avec ce choix de type cette fonction est l'identité. *)
let cnf_of_int_list_list (l: int list list) : cnf = l

(** print_modele : resultat -> unit afficher le résultat *)
let print_modele: resultat -> unit = function
  | Unsat   -> print_string "UNSAT\n"
  | Sat modele -> print_string "SAT\n";
     let modele_trie = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele_trie;
     print_string "0\n"

(** simplifie : literal -> cnf -> cnf 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)

let simplifie l clauses =
  (*on reverse le résultat de filter car filter_map inverse l'ordre de la liste*)
    List.rev (filter_map(fun clause -> 
      if List.mem l clause (*si on trouve le littéral dans la clause*)
        then None (*on le supprime*)
      else 
        let nouvelles_clauses = List.filter (fun litt -> litt != (-l)) clause (*On crée une nouvelle liste de clauses sans la négation du littéral à simplifier et recopie tout le reste*)
      in Some nouvelles_clauses ) clauses) 
    
     
    
  
(** solveur_split_rec : cnf -> interpretation -> resultat
   exemple d'utilisation de `simplifie' cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Sat interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then Unsat else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split_rec (simplifie l clauses) (l::interpretation) in
  match branche with
  | Unsat -> solveur_split_rec (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

let solveur_split clauses = solveur_split_rec clauses []

(** Solveur dpll récursif *)

(*Fonction auxiliaire pour vérifier si un littéral est pur*)
(** est_pur : int -> cnf -> boolean
   - si -x est présent, retourne false
   - sinon, retourne true *)
let rec est_pur x clauses = match clauses with
  |[] -> true
  |clause::reste -> if List.mem (-x) clause then false else est_pur x reste


(** pur : cnf -> literal optio
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon renvoie None *)
let pur clauses =
  let rec parcours_clauses c = match c with
    |[] -> None (*plus aucune clause*)
    |clause::reste_clauses ->
        let rec parcours_litteraux litt = match litt with (*on parcourt tous les littéraux de la clause courante*)
          |[] -> parcours_clauses reste_clauses (*clause suivante*)
          |a::reste_litt -> if est_pur a clauses then Some a (*s'il est pur on le retourne*)
              else parcours_litteraux reste_litt in parcours_litteraux clause (*on continue dans la clause courante*)
  in parcours_clauses clauses (*on repasse dans la totalité des clauses*)

(** unitaire : cnf -> literal option
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon renvoie None *)
let rec unitaire clauses = match clauses with
  | [] -> None (*cas de base : pas de clause dans clauses*)
  | clause::reste_clauses ->
      match clause with 
     | [litt] -> Some litt (*clause unitaire trouvée, un littéral de longueur 1, donc on le renvoie*)
     | _ -> unitaire reste_clauses (*sinon on continue la recherche récursivement*)
    
(** solveur_dpll_rec : cnf -> interpretation -> resultat *)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Sat interpretation 
  (* la clause vide n'est jamais satisfiable*)
  else if List.mem [] clauses then Unsat 
  else 
    (*algorithme DPLL*)
    (* 1- Les clauses unitaires*)
    match unitaire clauses with  
    | Some l -> solveur_dpll_rec (simplifie l clauses) (l::interpretation) (*si on trouve une clause unitaire, on simplifie*)
    (* 2- Les littéraux purs*)
    | None -> match pur clauses with 
            | Some l -> solveur_dpll_rec (simplifie l clauses) (l::interpretation) (*si on trouve un littéral pur, on simplifie *)
            | None -> 
              (* 3- branchement : l ou -l *) 
              let l = hd (hd clauses) in
              let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
              match branche with
              | Unsat -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
              | _    -> branche
                     

let solveur_dpll clauses = solveur_dpll_rec clauses []


(* --------------------- Tests pour la fonction pur ------------------------------*)

(*Vide*)
let%test "pur vide" = pur [] = Some 1

(*Un seul littéral positif*)
let%test "pur un seul littéral positif" = pur [[1]] = Some 1

(*Un seul littéral négatif*)
let%test "pur un seul littéral négatif" = pur [[-1]] = Some (-1)

(*Deux littéraux purs différents *)
let%test "pur deux littéraux purs" = 
  let result = pur [[1]; [2]] in
  result = Some 1 || result = Some 2

(*Un littéral pur*)
let%test "pur avec littéral pur" =
  let result = pur [[1;2];[3;5];[-2;8]] in result= Some 1 || result=Some 3 || result=Some 5 || result=Some 8

(*Aucun littéral pur*)
let%test "pur sans littéral pur" = 
  pur [[1; 2]; [-1; -2]; [3; -3]] = None
  
(*Plusieurs littéraux purs*)
let%test "pur plusieurs purs" = 
  let result = pur [[1; 4]; [2; 5]; [3; 6]] in match result with
  |Some x -> List.mem x [1; 2; 3; 4; 5; 6]
  |None -> false

(* --------------------- Tests pour la fonction unitaire ------------------------------*)

(* Vide *)
let%test "unitaire : vide" = unitaire[] = None

(* Aucune clause unitaire *)
let%test "unitaire : aucune clause unitaire" = unitaire[[3;4;-1];[6;3];[-7;2]] = None

(* Une seule clause unitaire *)
let%test "unitaire : une seule clause unitaire" = unitaire[[1]] = Some 1

(* 1ère clause pas unitaire et 2ème clause unitaire *)
let%test "unitaire : première clause non unitaire - deuxième clause unitaire" = unitaire [[3;5];[-6];[3;4]] = Some (-6)

(* Plusieurs clauses unitaires *)
let%test "unitaire : plusieurs clauses unitaires" = match unitaire [[4];[-3];[-5;6]] with 
| Some x -> List.mem x [4;-3] (*Selon l'ordre du parcours*) 
| None -> false

(* Présence de clause vide *)
let%test "unitaire : présence de clause vide " = unitaire [[];[2;3]] = None
let%test "unitaire : présence de clause vide " = unitaire [[];[1]] = Some 1

(* --------------------- Tests pour la fonction simplifie -----------------------------*)

(*Vide*)
let%test "simplifie : vide" = simplifie 1 [] = []

(*Simplifie 1 littéral au début de la liste*)
let%test "simplifie : littéral au début de la liste " = simplifie 4 [[4]; [-7;2]] = [[-7;2]]


(*Simplifie 1 littéral d'une clause unitaire*)
let%test "simplifie : 1 littéral de clause unitaire" = simplifie 4 [[3;1];[4]; [-7;2]] = [[3;1];[-7;2]]

(*Simplifie 1 littéral  et sa négation *)
let%test "simplifie : 1 littéral et sa négation" = simplifie 2 [[-2;1;4];[4];[-7;2];[-1;-2]] = [[1;4];[4];[-1]]

(**)

(*
(* Ceci est un exemple de test unitaire pour la fonction filter_map. *)
let%test "filter_map" =
  (filter_map (fun x -> if x mod 2 = 0 then Some (x * 2) else None) [1; 2; 3; 4]) = [8; 4]

(* Voici d'autres exemples de tests unitaires dont vous pouvez vous inspirer pour tester vos fonctions. *)
let rec big_list n acc =
  if n <= 0 then acc else big_list (n-1) (n::acc)

(* On teste d'abord sur une petite liste.*)
let %test "length vide" = (length [] = 0)
let %test "length 1" = (length [1] = 1)
let %test "length 3" = (length [1;2;3] = 3)
(* Puis sur une grande liste pour vérifier qu'il n'y a pas de débordement de pile. *)
   let %test "length big" = let big = 10000000 in (length (big_list big []) = big)
*)
 
