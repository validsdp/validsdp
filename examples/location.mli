(** Locations to keep track of position of code in original source file. *)

type t  (** Type of locations. *)

module Map : Map.S with type key = t  (** Maps from locations. *)

(** Dummy location. *)
val dummy : t

(** [beg_p l] returns a location representing the point at beginning of [l]. *)
val beg_p : t -> t

(** [end_p l] returns a location representing the point at the end of [l]. *)
val end_p : t -> t

(** The filename which will be registered in all subsequent calls to
    [get_current*]. *)
val filename : string ref

(** [get_current ()] returns current location in file [filename] during parsing.
    To be called in a parser rule. *)
val get_current : unit -> t

(** [get_current_from_lexbuf lexbuf] returns current location
    of lexer in file [filename]. Useful for lexing errors. *)
val get_current_from_lexbuf : Lexing.lexbuf -> t

(** Outputs a location. *)
val fprint : Format.formatter -> t -> unit
