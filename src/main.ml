
open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;

   
let leer_hasta_punto_y_coma () =
  let buffer = Buffer.create 256 in  (* Crear un buffer para acumular las líneas *)

  let rec leer () =
    try
      let linea = read_line () in  (* Leer una línea de la entrada estándar *)
      match String.index_opt linea ';' with
      | Some i ->
          (* Si se encuentra ';', agregar la parte antes del ';' sin saltos de línea *)
          let parte = String.sub linea 0 i in
          Buffer.add_string buffer parte;
          ()
      | None ->
          (* Si no se encuentra ';', agregar la línea completa sin agregar '\n' *)
          Buffer.add_string buffer linea;
          leer ()  (* Continuar leyendo *)
    with
    | End_of_file ->
        ()  (* Manejar el fin de archivo sin encontrar ';' *)
  in

  leer ();  (* Iniciar la lectura *)
  Buffer.contents buffer  (* Devolver el contenido acumulado como string *)

let top_level_loop () =
  print_endline "Evaluator of lambda expressions...";
  let rec loop ctx =
    print_string ">> ";
    flush stdout;
    try
      let c = s token (from_string (leer_hasta_punto_y_coma ())) in
      loop (execute ctx c)
    with
       Lexical_error ->
         print_endline "lexical error";
         loop ctx
     | Parse_error ->
         print_endline "syntax error";
         loop ctx
     | Type_error e ->
         print_endline ("type error: " ^ e);
         loop ctx
     | End_of_file ->
         print_endline "...bye!!!"
  in
    loop emptyctx
  ;;

top_level_loop ()
;;
