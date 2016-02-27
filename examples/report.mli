(** Module providing functions to print errors in a way the compilation mode
    of Emacs understands while handling verbosity level and locations. *)

(** Exception raised after printing an error message. *)
exception Error

(** Verbosity level. Defines the amount of logging messages outputed.
    Default is 1. 0 means quiet (only warning and error messages get printed). *)
val verbosity : int ref

(** [nflogf n f <args>] prints a log message like [Format.eprintf]
    if [n] is greater or equal to [verbosity].

    Starting from level 4, the message is also indented from 2*(n-3) spaces. *)
val nlogf : int -> ('a, Format.formatter, unit) format -> 'a

(** Prints a warning message. *)
val warning : ('a, Format.formatter, unit) format -> 'a

(** Prints a warning message along with location. *)
val warning_loc : Location.t -> ('a, Format.formatter, unit) format -> 'a

(** Prints an error message. *)
val error : ('a, Format.formatter, unit, 'b) format4 -> 'a

(** Prints an error message along with location and raises [Error]. *)
val error_loc : Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(** [silent f] executes function [f] without printing any log message. *)
val silent : (unit -> 'a) -> 'a
