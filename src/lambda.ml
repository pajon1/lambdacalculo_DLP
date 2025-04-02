(* lambda.ml *)

(* TYPE DEFINITIONS *)

type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString
  | TyTuple of ty list
  | TyRecord of (string * ty) list
  | TyList of ty
  | TyVariant of (string * ty) list
  | TyVar of string
  | TyTop               
  | TyBot              
;;

type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmVar of string
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLetIn of string * term * term
  | TmFix of term
  | TmString of string
  | TmConcat of term * term
  | TmTuple of term list
  | TmRecord of (string * term) list
  | TmProj of term * int
  | TmRProj of term * string
  | TmCons of ty * term * term
  | TmNil of ty
  | TmHead of ty * term
  | TmTail of ty * term
  | TmIsNil of ty * term
  | TmTag of string * term * ty
  | TmCase of term * (string * string * term) list
;;

type command =
    Eval of term
  | Bind of string * term
  | BindType of string * ty
  | Quit
;;

type binding =
    TyBind of ty
  | TyTmBind of (ty * term)
;;

type context =
  (string * binding) list
;;


(* CONTEXT MANAGEMENT *)

let emptyctx = []

let addtbinding ctx s ty =
  (s, TyBind ty) :: ctx

let addvbinding ctx s ty tm =
  (s, TyTmBind (ty, tm)) :: ctx

let gettbinding ctx s =
  match List.assoc s ctx with
      TyBind ty -> ty
    | TyTmBind (ty, _) -> ty

let getvbinding ctx s =
  match List.assoc s ctx with
      TyTmBind (_, tm) -> tm
    | _ -> raise Not_found


(* TYPE MANAGEMENT (TYPING) *)

let pretty_printer cadena =
  cadena

let rec string_of_ty ty = match ty with
    TyBool ->
      "Bool"
  | TyNat ->
      "Nat"
  | TyArr (ty1, ty2) ->
      let s1 = match ty1 with
          TyArr _ -> "(" ^ string_of_ty ty1 ^ ")"
        | _ -> string_of_ty ty1
      in
      s1 ^ " -> " ^ string_of_ty ty2
  | TyString ->
      "String"
  | TyTuple t ->
    let rec aux str l first =
      match l with
      | [] -> str ^ "}"
      | h :: tail ->
          if first = 1 then
            aux (str ^ string_of_ty h) tail 0
          else
            aux (str ^ "," ^ string_of_ty h) tail 0
    in
    aux "{" t 1
  | TyRecord (t) ->
  	let rec aux str l first =
  	match l with
  	| [] -> str ^ " }"
  	| (name,ty)::tail -> if first = 1 then aux (str ^ name ^ ": " ^ string_of_ty ty) tail 0 else aux (str ^ ", " ^ name ^ ": " ^ string_of_ty ty) tail 0
  	in aux "{ " t 1
  | TyList ty_inner ->
      "List[" ^ string_of_ty ty_inner ^ "]"
  | TyVariant field_types ->
      let field_strings = List.map (fun (l_i, t_i) -> l_i ^ " : " ^ string_of_ty t_i) field_types in
      "<" ^ String.concat ", " field_strings ^ ">"
  | TyVar s ->
      s
  | TyTop -> "Top"        (* NUEVO *)
  | TyBot -> "Bot"        (* NUEVO *)
;;

exception Type_error of string

let rec resolve_type ctx ty = match ty with
    TyVar s ->
      (try
         let ty' = gettbinding ctx s in
         resolve_type ctx ty'
       with
         | Not_found -> raise (Type_error ("Unbound type variable: " ^ s)))
    | TyArr (ty1, ty2) ->
        TyArr (resolve_type ctx ty1, resolve_type ctx ty2)
    | TyList ty_inner ->
        TyList (resolve_type ctx ty_inner)
    | TyTuple tys ->
        TyTuple (List.map (resolve_type ctx) tys)
    | TyVariant fields ->
        TyVariant (List.map (fun (l, ty) -> (l, resolve_type ctx ty)) fields)
    | _ -> ty

(* NUEVO: Funciones auxiliares para subtipado *)

let sort_fields fields =
  List.sort (fun (l1,_) (l2,_) -> compare l1 l2) fields

(* Comprueba que los campos de tfields estén en sfields y subtipados adecuadamente *)
let rec is_subfields ctx sfields tfields =
  match (sfields, tfields) with
  | (_, []) -> true
  | ((l_s, ty_s)::ss, (l_t, ty_t)::ts) ->
      let c = compare l_s l_t in
      if c = 0 then 
        (* Mismo label, comprobar subtipado de tipos de campo *)
        if is_subtype ctx ty_s ty_t then is_subfields ctx ss ts
        else false
      else if c < 0 then
        (* Campo extra en S, ignoramos y seguimos buscando *)
        is_subfields ctx ss ((l_t, ty_t)::ts)
      else
        (* T tiene un campo que S no tiene *)
        false
  | ([], _) ->
      false

(* NUEVO: Implementar is_subtype *)
and is_subtype ctx s t =
  let s = resolve_type ctx s in
  let t = resolve_type ctx t in
  if equal_types ctx s t then true else
  match (s, t) with
  | (_, TyTop) ->
      (* S<:Top siempre *)
      true

  | (TyBot, _) ->
      (* Bot<:T siempre *)
      true

  | (TyArr(s1, s2), TyArr(t1, t2)) ->
      (* (S1->S2)<:(T1->T2) si T1<:S1 y S2<:T2 *)
      (is_subtype ctx t1 s1) && (is_subtype ctx s2 t2)

  | (TyRecord sfields, TyRecord tfields) ->
      (* Subtipado de registros: check R-Width, R-Depth (S<:T si T es un "subconjunto" de S y los tipos son subtipados) *)
      let sfields_sorted = sort_fields sfields in
      let tfields_sorted = sort_fields tfields in
      is_subfields ctx sfields_sorted tfields_sorted

  | (TyVariant sfields, TyVariant tfields) ->
      (* Subtipado de variantes: similar a registros en este ejemplo *)
      let sfields_sorted = sort_fields sfields in
      let tfields_sorted = sort_fields tfields in
      is_subfields ctx sfields_sorted tfields_sorted

  | _ ->
      false

(* Ajustamos equal_types para no romper el código existente: ahora equal_types es igualdad estricta,
   mientras que subtipado se maneja por is_subtype. *)
and equal_types ctx ty1 ty2 =
  let ty1 = resolve_type ctx ty1 in
  let ty2 = resolve_type ctx ty2 in
  match ty1, ty2 with
  | TyBool, TyBool -> true
  | TyNat, TyNat -> true
  | TyString, TyString -> true
  | TyVar s1, TyVar s2 -> s1 = s2
  | TyArr (ty1a, ty1b), TyArr (ty2a, ty2b) ->
      equal_types ctx ty1a ty2a && equal_types ctx ty1b ty2b
  | TyTuple tys1, TyTuple tys2 ->
      List.length tys1 = List.length tys2 &&
      List.for_all2 (equal_types ctx) tys1 tys2
  | TyList ty1_inner, TyList ty2_inner ->
      equal_types ctx ty1_inner ty2_inner
  | TyVariant fields1, TyVariant fields2 ->
      let sorted_fields1 = List.sort compare fields1 in
      let sorted_fields2 = List.sort compare fields2 in
      List.length sorted_fields1 = List.length sorted_fields2 &&
      List.for_all2 (fun (l1, ty1) (l2, ty2) ->
          l1 = l2 && equal_types ctx ty1 ty2
      ) sorted_fields1 sorted_fields2
  | TyVar s, ty | ty, TyVar s ->
      let resolved_ty = resolve_type ctx (TyVar s) in
      if resolved_ty = TyVar s then false else equal_types ctx resolved_ty ty
  | TyTop, TyTop -> true
  | TyBot, TyBot -> true
  | _, _ -> false

(* MODIFICAMOS typeof: Donde antes usábamos equal_types para chequear igualdad exacta, 
   ahora usamos is_subtype para permitir subtipado. *)

let rec typeof ctx tm = match tm with
    TmTrue ->
      TyBool

  | TmFalse ->
      TyBool

  | TmIf (t1, t2, t3) ->
      (* Para if: la condición debe ser Bool *)
      if is_subtype ctx (typeof ctx t1) TyBool then
        let tyT2 = typeof ctx t2 in
        let tyT3 = typeof ctx t3 in
        (* Si t2: S y t3: U, el tipo del if debe ser el "join" si existe,
           pero aquí simplificamos: si uno es subtipo del otro, devolvemos el supertipo. *)
        if is_subtype ctx tyT2 tyT3 then tyT3
        else if is_subtype ctx tyT3 tyT2 then tyT2
        else raise (Type_error "arms of conditional have incompatible types")
      else
        raise (Type_error "guard of conditional not a boolean")

  | TmZero ->
      TyNat

  | TmSucc t1 ->
      if is_subtype ctx (typeof ctx t1) TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")

  | TmPred t1 ->
      if is_subtype ctx (typeof ctx t1) TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")

  | TmIsZero t1 ->
      if is_subtype ctx (typeof ctx t1) TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")

  | TmVar x ->
      (try gettbinding ctx x with
       _ -> raise (Type_error ("no binding type for variable " ^ x)))

  | TmAbs (x, tyT1, t2) ->
      let ctx' = addtbinding ctx x tyT1 in
      let tyT2 = typeof ctx' t2 in
      TyArr (tyT1, tyT2)

  | TmApp (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
       | TyArr (tyT11, tyT12) ->
           (* Antes pedíamos igualdad exacta, ahora pedimos tyT2<:tyT11 *)
           if is_subtype ctx tyT2 tyT11 then tyT12
           else raise (Type_error "parameter type mismatch")
       | _ -> raise (Type_error "arrow type expected"))

  | TmLetIn (x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let ctx' = addtbinding ctx x tyT1 in
      typeof ctx' t2

  | TmFix t1 ->
      let tyT1 = typeof ctx t1 in
      (match tyT1 with
        TyArr (tyT11, tyT12) ->
          (* Para fix, requerimos tyT11<:tyT12 y tyT12<:tyT11 para que sean equivalentes *)
          if is_subtype ctx tyT11 tyT12 && is_subtype ctx tyT12 tyT11 then tyT12
          else raise (Type_error "result of body not compatible with domain")
      | _ -> raise (Type_error "arrow type expected"))

  | TmString _ ->
      TyString

  | TmConcat (t1, t2) ->
      if is_subtype ctx (typeof ctx t1) TyString && is_subtype ctx (typeof ctx t2) TyString then TyString
      else raise (Type_error "arguments of concat are not strings")

  | TmTuple t1 ->
      let ty =
        let rec aux tyt t =
          match t with
          | [] -> List.rev tyt
          | h :: tail -> aux ((typeof ctx h) :: tyt) tail
        in
        aux [] t1
      in
      TyTuple ty

  | TmRecord t1 ->
      let ty =
        let rec aux tyr t =
          match t with
          | [] -> List.rev tyr
          | (name,tname)::tail -> aux ((name,(typeof ctx tname))::tyr) tail
        in aux [] t1
      in TyRecord (ty)

  | TmProj (t1, t2) ->
      (match typeof ctx t1 with
       | TyTuple ttys ->
           if List.length ttys > t2 then List.nth ttys t2
           else raise (Type_error "not enough elements in the tuple")
       | _ -> raise (Type_error "tuple type expected"))

  | TmCons (ty, head, tail) ->
      if is_subtype ctx (typeof ctx head) ty &&
         is_subtype ctx (typeof ctx tail) (TyList ty) then TyList ty
      else raise (Type_error "cons type error")

  | TmNil ty ->
      TyList ty

  | TmHead (ty, t1) ->
      (match typeof ctx t1 with
       | TyList ty_elem -> ty_elem
       | _ -> raise (Type_error "head expects a list"))

  | TmTail (_, t1) ->
      (match typeof ctx t1 with
       | TyList ty_elem -> TyList ty_elem
       | _ -> raise (Type_error "tail expects a list"))

  | TmIsNil (_, t1) ->
      (match typeof ctx t1 with
       | TyList _ -> TyBool
       | _ -> raise (Type_error "isnil expects a list"))

  | TmTag (l_i, t_i, tyT) ->
      let tyT_resolved = resolve_type ctx tyT in
      (match tyT_resolved with
       | TyVariant field_types ->
           (try
              let t_expected = List.assoc l_i field_types in
              let ty_ti = typeof ctx t_i in
              if is_subtype ctx ty_ti t_expected then tyT_resolved
              else raise (Type_error ("Type mismatch in variant tag for label " ^ l_i))
            with Not_found ->
              raise (Type_error ("Label " ^ l_i ^ " not found in variant type")))
       | _ -> raise (Type_error "Expected variant type after 'as' in tagging"))

  | TmCase (t0, cases) ->
      let tyT0 = typeof ctx t0 in
      let tyT0_resolved = resolve_type ctx tyT0 in
      (match tyT0_resolved with
       | TyVariant field_types ->
           let result_type = ref None in
           List.iter (fun (li, xi, ti) ->
             try
               let t_expected = List.assoc li field_types in
               let ctx' = addtbinding ctx xi t_expected in
               let ty_ti = typeof ctx' ti in
               (match !result_type with
                | None -> result_type := Some ty_ti
                | Some ty ->
                    if is_subtype ctx ty_ti ty && is_subtype ctx ty ty_ti then ()
                    else raise (Type_error "Branches of case have incompatible types"))
             with Not_found ->
               raise (Type_error ("Label " ^ li ^ " not found in variant type")))
           cases;
           (match !result_type with
            | None -> raise (Type_error "Case expression has no branches")
            | Some ty -> ty)
       | _ -> raise (Type_error "Case expression applied to non-variant type"))

  | TmRProj (t, label) ->
      (match typeof ctx t with
       | TyRecord fields ->
           (try List.assoc label fields
            with Not_found -> raise (Type_error ("Label " ^ label ^ " not found in record type")))
       | _ -> raise (Type_error "Projection on non-record type"))

;;


(* TERMS MANAGEMENT (EVALUATION) *)

let indent n = String.make (n * 2) ' '

let rec string_of_term_at_level indent_level tm = match tm with
    TmTrue ->
      indent indent_level ^ "true"
  | TmFalse ->
      indent indent_level ^ "false"
  | TmIf (t1, t2, t3) ->
      indent indent_level ^ "if " ^ string_of_term indent_level t1 ^ "\n" ^
      indent indent_level ^ "then\n" ^
      string_of_term_at_level (indent_level + 1) t2 ^ "\n" ^
      indent indent_level ^ "else\n" ^
      string_of_term_at_level (indent_level + 1) t3
  | TmZero ->
      indent indent_level ^ "0"
  | TmSucc t ->
     let rec f n t' = match t' with
          TmZero -> indent indent_level ^ string_of_int n
        | TmSucc s -> f (n+1) s
        | _ -> indent indent_level ^ "succ " ^ string_of_term indent_level t
      in f 1 t
  | TmPred t ->
      indent indent_level ^ "pred " ^ string_of_term indent_level t
  | TmIsZero t ->
      indent indent_level ^ "iszero " ^ string_of_term indent_level t
  | TmVar s ->
      indent indent_level ^ s
  | TmAbs (s, tyS, t) ->
      indent indent_level ^ "lambda " ^ s ^ ":" ^ string_of_ty tyS ^ ".\n" ^
      string_of_term_at_level (indent_level + 1) t
  | TmApp (t1, t2) ->
      let s1 = match t1 with
          TmAbs _ | TmIf _ | TmLetIn _ | TmFix _ -> "(" ^ string_of_term indent_level t1 ^ ")"
        | _ -> string_of_term indent_level t1
      in
      let s2 = match t2 with
          TmAbs _ | TmIf _ | TmLetIn _ | TmFix _ | TmApp _ -> "\n"^indent indent_level^"(" ^ string_of_term indent_level t2 ^ ")"
        | _ -> string_of_term indent_level t2
      in
      indent indent_level ^ s1 ^ " " ^ s2
  | TmLetIn (s, t1, t2) ->
      indent indent_level ^ "let " ^ s ^ " = " ^ string_of_term indent_level t1 ^ " in\n" ^
      string_of_term_at_level (indent_level + 1) t2
  | TmFix t ->
      indent indent_level ^ "fix\n" ^string_of_term_at_level (indent_level + 1) t
  | TmString s ->
      indent indent_level ^ "\"" ^ s ^ "\""
  | TmConcat (t1, t2) ->
      indent indent_level ^ "concat " ^ string_of_term indent_level t1 ^ " " ^ string_of_term indent_level t2
  | TmTuple t ->
    let rec aux str l first =
      match l with
      | [] -> str ^ "}"
      | h :: tail ->
          if first = 1 then
            aux (str ^ string_of_term indent_level h) tail 0
          else
            aux (str ^ "," ^ string_of_term indent_level h) tail 0
    in
    aux "{" t 1
	
  | TmRecord (t) ->
  	let rec aux str l first = 
  	match l with
  	| [] -> str ^ "}"
  	| (name, t')::tail -> if first = 1 then aux (str ^ name ^ ": " ^ (string_of_term indent_level t')) tail 0 else aux (str ^ ", " ^ name ^ ": " ^ (string_of_term indent_level t')) tail 0
  	in aux "{ " t 1
  	
  | TmProj (t1, t2) ->
      string_of_term indent_level t1 ^ "." ^ string_of_int t2
  	
  | TmRProj (t, name) ->
  	string_of_term indent_level t ^ "." ^ name
  	
  (* Nuevos casos para listas *)
  | TmCons (ty, head, tail) ->
      indent indent_level ^ "cons[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level head ^ " " ^ string_of_term indent_level tail
  | TmNil ty ->
      indent indent_level ^ "nil[" ^ string_of_ty ty ^ "]"
  | TmHead (ty, t1) ->
      indent indent_level ^ "head[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level t1
  | TmTail (ty, t1) ->
      indent indent_level ^ "tail[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level t1
  | TmIsNil (ty, t1) ->
      indent indent_level ^ "isnil[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level t1
  | TmTag (l, t, tyT) ->
      indent indent_level ^ "<" ^ l ^ " = " ^ string_of_term indent_level t ^ "> as " ^ string_of_ty tyT
  | TmCase (t0, cases) ->
      indent indent_level ^ "case " ^ string_of_term indent_level t0 ^ " of\n" ^
      String.concat "\n" (List.map (fun (li, xi, ti) ->
        indent (indent_level + 1) ^ "<" ^ li ^ " = " ^ xi ^ "> =>\n" ^ string_of_term_at_level (indent_level + 2) ti) cases)
and string_of_term indent_level tm = match tm with
    TmTrue ->
      "true"
  | TmFalse ->
      "false"
  | TmIf (t1, t2, t3) ->
      "if " ^ string_of_term indent_level t1 ^ "\n" ^
      "then\n" ^
      string_of_term_at_level (indent_level + 1) t2 ^ "\n" ^
      "else\n" ^
      string_of_term_at_level (indent_level + 1) t3
  | TmZero ->
      "0"
  | TmSucc t ->
     let rec f n t' = match t' with
          TmZero -> string_of_int n
        | TmSucc s -> f (n+1) s
        | _ -> "succ " ^ string_of_term indent_level t
      in f 1 t
  | TmPred t ->
      "pred " ^ string_of_term indent_level t
  | TmIsZero t ->
      "iszero " ^ string_of_term indent_level t
  | TmVar s ->
       s
  | TmAbs (s, tyS, t) ->
      "lambda " ^ s ^ ":" ^ string_of_ty tyS ^ ".\n" ^
      string_of_term_at_level (indent_level + 1) t
  | TmApp (t1, t2) ->
      let s1 = match t1 with
          TmAbs _ | TmIf _ | TmLetIn _ | TmFix _ -> "(" ^ string_of_term indent_level t1 ^ ")"
        | _ -> string_of_term indent_level t1
      in
      let s2 = match t2 with
          TmAbs _ | TmIf _ | TmLetIn _ | TmFix _ | TmApp _ -> "\n"^indent indent_level^"(" ^ string_of_term indent_level t2 ^ ")"
        | _ -> string_of_term indent_level t2
      in
      s1 ^ " " ^ s2
  | TmLetIn (s, t1, t2) ->
      "let " ^ s ^ " = " ^ string_of_term indent_level t1 ^ " in\n" ^
      string_of_term_at_level (indent_level + 1) t2
  | TmFix t ->
      "fix\n" ^string_of_term_at_level (indent_level + 1) t
  | TmString s ->
      "\"" ^ s ^ "\""
  | TmConcat (t1, t2) ->
      "concat " ^ string_of_term indent_level t1 ^ " " ^ string_of_term indent_level t2
  | TmTuple t ->
    let rec aux str l first =
      match l with
      | [] -> str ^ "}"
      | h :: tail ->
          if first = 1 then
            aux (str ^ string_of_term indent_level h) tail 0
          else
            aux (str ^ "," ^ string_of_term indent_level h) tail 0
    in
    aux "{" t 1
	
  | TmRecord (t) ->
  	let rec aux str l first = 
  	match l with
  	| [] -> str ^ "}"
  	| (name, t')::tail -> if first = 1 then aux (str ^ name ^ ": " ^ (string_of_term indent_level t')) tail 0 else aux (str ^ ", " ^ name ^ ": " ^ (string_of_term indent_level t')) tail 0
  	in aux "{ " t 1
  
  | TmProj (t1, t2) ->
      string_of_term indent_level t1 ^ "." ^ string_of_int t2
  
  | TmRProj (t, name) ->
  	string_of_term indent_level t ^ "." ^ name
  
  (* Nuevos casos para listas *)
  
  | TmCons (ty, head, tail) ->
      "cons[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level head ^" "^string_of_term indent_level tail
  
  | TmNil ty ->
      "nil[" ^ string_of_ty ty ^ "]"
  
  (* Nuevos casos para head, tail e isnil *)
  
  | TmHead (ty, t1) ->
      "head[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level t1
  
  | TmTail (ty, t1) ->
      "tail[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level t1
  
  | TmIsNil (ty, t1) ->
      "isnil[" ^ string_of_ty ty ^ "] " ^ string_of_term indent_level t1
  | TmTag (l, t, tyT) ->
      "<" ^ l ^ " = " ^ string_of_term indent_level t ^ "> as " ^ string_of_ty tyT
  | TmCase (t0, cases) ->
      "case " ^ string_of_term indent_level t0 ^ " of\n" ^
      String.concat "\n" (List.map (fun (li, xi, ti) ->
        "<" ^ li ^ " = " ^ xi ^ "> =>\n" ^ string_of_term_at_level (indent_level + 1) ti) cases)
;;

let rec ldif l1 l2 = match l1 with
    [] -> []
  | h :: t -> if List.mem h l2 then ldif t l2 else h :: (ldif t l2)
;;

let rec lunion l1 l2 = match l1 with
    [] -> l2
  | h :: t -> if List.mem h l2 then lunion t l2 else h :: (lunion t l2)
;;

let rec free_vars tm = match tm with
    TmTrue ->
      []
  | TmFalse ->
      []
  | TmIf (t1, t2, t3) ->
      lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero ->
      []
  | TmSucc t ->
      free_vars t
  | TmPred t ->
      free_vars t
  | TmIsZero t ->
      free_vars t
  | TmVar s ->
      [s]
  | TmAbs (s, _, t) ->
      ldif (free_vars t) [s]
  | TmApp (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmLetIn (s, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)
  | TmFix t ->
      free_vars t
  | TmString _ ->
      []
  | TmConcat (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmTuple t ->
      List.fold_left (fun acc h -> lunion acc (free_vars h)) [] t
  | TmRecord t ->
      let rec aux vars record =
        match record with
        | (name, t')::tail -> aux (lunion (free_vars t') vars) tail
        | [] -> vars
      in aux [] t
  | TmProj (t1, t2) ->
      free_vars t1
  
  (* Nuevos casos para listas *)
  | TmCons (_, h, t) ->
      lunion (free_vars h) (free_vars t)
  | TmNil _ ->
      []
  | TmHead (_, t1) ->
      free_vars t1
  | TmTail (_, t1) ->
      free_vars t1
  | TmIsNil (_, t1) ->
      free_vars t1
  | TmTag (_, t, _) ->
      free_vars t
  | TmCase (t0, cases) ->
      let fvs_t0 = free_vars t0 in
      let fvs_cases = List.fold_left (fun acc (li, xi, ti) ->
        let fvs_ti = ldif (free_vars ti) [xi] in
        lunion acc fvs_ti) [] cases in
      lunion fvs_t0 fvs_cases

  (* Nuevo caso para TmRProj *)
  | TmRProj (t, _) ->
      free_vars t
;;


let rec fresh_name x l =
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;

let rec subst x s tm = match tm with
    TmTrue ->
      TmTrue
  | TmFalse ->
      TmFalse
  | TmIf (t1, t2, t3) ->
      TmIf (subst x s t1, subst x s t2, subst x s t3)
  | TmZero ->
      TmZero
  | TmSucc t ->
      TmSucc (subst x s t)
  | TmPred t ->
      TmPred (subst x s t)
  | TmIsZero t ->
      TmIsZero (subst x s t)
  | TmVar y ->
      if y = x then s else tm
  | TmAbs (y, tyY, t) ->
      if y = x then tm
      else
        let fvs = free_vars s in
        if not (List.mem y fvs)
        then TmAbs (y, tyY, subst x s t)
        else
          let z = fresh_name y (free_vars t @ fvs) in
          TmAbs (z, tyY, subst x s (subst y (TmVar z) t))
  | TmApp (t1, t2) ->
      TmApp (subst x s t1, subst x s t2)
  | TmLetIn (y, t1, t2) ->
      if y = x then TmLetIn (y, subst x s t1, t2)
      else
        let fvs = free_vars s in
        if not (List.mem y fvs)
        then TmLetIn (y, subst x s t1, subst x s t2)
        else
          let z = fresh_name y (free_vars t2 @ fvs) in
          TmLetIn (z, subst x s t1, subst x s (subst y (TmVar z) t2))
  | TmFix t ->
      TmFix (subst x s t)
  | TmString st ->
      TmString st
  | TmConcat (t1, t2) ->
      TmConcat (subst x s t1, subst x s t2)
      
  | TmTuple (t) ->
	let rec aux tup l =
	match l with
	| [] -> TmTuple (List.rev tup)
	| h::tail -> aux ((subst x s h)::tup) tail
	in aux [] t
	
   | TmRecord (t) ->
   	let rec aux record l =
   	match l with 
   	| [] -> TmRecord (List.rev record)
   	| (name, t')::tail -> aux ((name,(subst x s t'))::record) tail
   	in aux [] t
   
   | TmProj (t1, t2) ->
   	TmProj (subst x s t1, t2)
   
   | TmRProj (t1, t2) ->
   	TmRProj (subst x s t1, t2)
   
   (* Nuevos casos para listas *)
  | TmCons (ty, h, t) ->
      TmCons (ty, subst x s h, subst x s t)
  | TmNil ty ->
      TmNil ty
  | TmHead (ty, t1) ->
      TmHead (ty, subst x s t1)
  | TmTail (ty, t1) ->
      TmTail (ty, subst x s t1)
  | TmIsNil (ty, t1) ->
      TmIsNil (ty, subst x s t1)
  | TmTag (l, t, tyT) ->
      TmTag (l, subst x s t, tyT)
  | TmCase (t0, cases) ->
      let t0' = subst x s t0 in
      let cases' = List.map (fun (li, xi, ti) ->
        if xi = x then (li, xi, ti)
        else (li, xi, subst x s ti)) cases in
      TmCase (t0', cases')
;;

let rec isnumericval tm = match tm with
    TmZero -> true
  | TmSucc t -> isnumericval t
  | _ -> false
;;

let rec isval tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | TmString _ -> true
  | TmTuple _ -> true
  | TmRecord _ -> true
  | TmNil _ -> true                          (* TmNil es un valor *)
  | TmCons (_, h, t) -> isval h && isval t  (* TmCons es un valor si sus componentes son valores *)
  | t when isnumericval t -> true
  | TmTag (_, v, _) when isval v -> true
  | _ -> false
;;

exception NoRuleApplies
;;

let rec eval1 ctx tm = match tm with
 (* E-IfTrue *)
    TmIf (TmTrue, t2, _) ->
      t2

    (* E-IfFalse *)
  | TmIf (TmFalse, _, t3) ->
      t3

    (* E-If *)
  | TmIf (t1, t2, t3) ->
      let t1' = eval1 ctx t1 in
      TmIf (t1', t2, t3)

    (* E-Succ *)
  | TmSucc t1 ->
      let t1' = eval1 ctx t1 in
      TmSucc t1'

    (* E-PredZero *)
  | TmPred TmZero ->
      TmZero

    (* E-PredSucc *)
  | TmPred (TmSucc nv1) when isnumericval nv1 ->
      nv1

    (* E-Pred *)
  | TmPred t1 ->
      let t1' = eval1 ctx t1 in
      TmPred t1'

    (* E-IszeroZero *)
  | TmIsZero TmZero ->
      TmTrue

    (* E-IszeroSucc *)
  | TmIsZero (TmSucc nv1) when isnumericval nv1 ->
      TmFalse

    (* E-Iszero *)
  | TmIsZero t1 ->
      let t1' = eval1 ctx t1 in
      TmIsZero t1'

    (* E-AppAbs *)
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 ->
      subst x v2 t12

    (* E-App2: evaluate argument before applying function *)
  | TmApp (v1, t2) when isval v1 ->
      let t2' = eval1 ctx t2 in
      TmApp (v1, t2')

    (* E-App1: evaluate function before argument *)
  | TmApp (t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmApp (t1', t2)

    (* E-LetV *)
  | TmLetIn (x, v1, t2) when isval v1 ->
      subst x v1 t2

    (* E-Let *)
  | TmLetIn(x, t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmLetIn (x, t1', t2)

    (* E-FixBeta *)
  | TmFix (TmAbs(x, _, t2)) ->
      subst x tm t2

    (* E-Fix *)
  | TmFix t1 ->
      let t1' = eval1 ctx t1 in
      TmFix t1'

    (* E-Concat *)
  | TmConcat (TmString s1, TmString s2) ->
     TmString (s1 ^ s2)

  | TmConcat (TmString s1, t2) ->
     let t2' = eval1 ctx t2 in
     TmConcat (TmString s1, t2')

  | TmConcat (t1, t2) -> 
     let t1' = eval1 ctx t1 in
     TmConcat (t1', t2)

   (* E-ProjTuple *)
  | TmProj(TmTuple(t1), t2) ->
    List.nth t1 t2

  | TmProj(t1, t2) ->
     let t1' = eval1 ctx t1 in
     TmProj(t1', t2)

   (*E-ProjRCD*)
  | TmRProj(TmRecord(t1), t2) ->
  	List.assoc t2 t1
     
     (*E-Proj record*)
  | TmRProj(t1, t2) ->
  	let t1' = eval1 ctx t1 in 
  	TmRProj(t1', t2)
   
   (*E-Tuple*)
  | TmTuple (t) ->
	let rec aux evs l =
	match l with 
	| [] -> TmTuple (List.rev evs)
	| h::tail -> aux ((eval1 ctx h)::evs) tail
	in aux [] t
	
    (*E-RCD*)
  | TmRecord (t) ->
  	let rec aux evs l =
  	match l with 
  	| [] -> TmRecord (List.rev evs)
  	| (name, t')::tail -> aux ((name,(eval1 ctx t'))::evs) tail
  	in aux [] t	
	
  (* Nuevos casos para listas *)
  
  | TmCons (_, v1, v2) when isval v1 && isval v2 ->
      raise NoRuleApplies  (* cons de valores es un valor, no hay reglas para reducir *)
  
  | TmCons (ty, h, t) ->
      if not (isval h) then
        let h' = eval1 ctx h in
        TmCons (ty, h', t)
      else if not (isval t) then
        let t' = eval1 ctx t in
        TmCons (ty, h, t')
      else
        raise NoRuleApplies

  | TmNil _ ->
      raise NoRuleApplies

  | TmHead (_, TmCons (_, v1, _)) when isval v1 ->
      v1
  | TmHead (_, TmNil _) ->
      raise NoRuleApplies
  | TmHead (ty, t1) ->
      let t1' = eval1 ctx t1 in
      TmHead (ty, t1')

  | TmTail (_, TmCons (_, _, v2)) when isval v2 ->
      v2
  | TmTail (_, TmNil _) ->
      raise NoRuleApplies
  | TmTail (ty, t1) ->
      let t1' = eval1 ctx t1 in
      TmTail (ty, t1')

  | TmIsNil (ty, TmNil _) ->
      TmTrue
  | TmIsNil (ty, TmCons (_, _, _)) ->
      TmFalse
  | TmIsNil (ty, t1) ->
      let t1' = eval1 ctx t1 in
      TmIsNil (ty, t1')

  (* E-VARIANT *)
  | TmTag (l, t_i, tyT) when not (isval t_i) ->
      let t_i' = eval1 ctx t_i in
      TmTag (l, t_i', tyT)

  (* E-CASE *)
  | TmCase (t0, cases) when not (isval t0) ->
      let t0' = eval1 ctx t0 in
      TmCase (t0', cases)

  (* E-CASEVARIANT *)
  | TmCase (TmTag (l_j, v_j, _), cases) when isval v_j ->
      (try
        let (_, x_j, t_j) = List.find (fun (li, xi, ti) -> li = l_j) cases in
        subst x_j v_j t_j
      with Not_found ->
        raise NoRuleApplies)

  | TmVar s ->
   (try 
      getvbinding ctx s 
    with Not_found -> raise NoRuleApplies)
  | _ ->
      raise NoRuleApplies
;;

let apply_ctx ctx tm =
   List.fold_left (fun t x ->
     try
       subst x (getvbinding ctx x) t
     with Not_found ->
       t
   ) tm (free_vars tm)
;;

let rec eval ctx tm =
  try
    let tm' = eval1 ctx tm in
    eval ctx tm'
  with
    NoRuleApplies -> apply_ctx ctx tm
;;

let execute ctx = function
    Eval tm ->
      let tyTm = typeof ctx tm in
      let tm' = eval ctx tm in
      print_endline ("- : " ^ string_of_ty tyTm ^ " =\n" ^ string_of_term 0 tm');
      ctx
  | Bind (s, tm) ->
      let tyTm = typeof ctx tm in
      let tm' = eval ctx tm in
      print_endline (s ^ " : " ^ string_of_ty tyTm ^ " =\n" ^ string_of_term 0 tm');
      addvbinding ctx s tyTm tm'
  | BindType (s, ty) ->
      print_endline ("type " ^ s ^ " = " ^ string_of_ty ty);
      addtbinding ctx s ty
  | Quit ->
      raise End_of_file
;;

