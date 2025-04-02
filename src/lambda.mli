(* lambda.mli *)

type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString
  | TyTuple of ty list
  | TyRecord of (string * ty) list
  | TyList of ty
  | TyVariant of (string * ty) list
  | TyVar of string          (* New constructor for type variables *)
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
  | TmTag of string * term * ty          (* New constructor for variants *)
  | TmCase of term * (string * string * term) list   (* New constructor for case analysis *)
;;

type command =
    Eval of term
  | Bind of string * term
  | BindType of string * ty   (* New constructor *)
  | Quit
;;

type binding =
    TyBind of ty
  | TyTmBind of (ty * term)
;;

type context =
  (string * binding) list
;;

val emptyctx : context;;
val addtbinding : context -> string -> ty -> context;;
val addvbinding : context -> string -> ty -> term -> context;;
val gettbinding : context -> string -> ty;;
val getvbinding : context -> string -> term;;

val string_of_ty : ty -> string;;
exception Type_error of string;;
val typeof : context -> term -> ty;;

val string_of_term : int -> term -> string;;
exception NoRuleApplies;;
val eval : context -> term -> term;;

val execute : context -> command -> context;;
