(** Parsing of matrix files. *)

(** [file filename] returns the matrices parsed from file [filename].

    Returns a list of triple [s, b, m] where [s] is an integer
    representing the size of the matrix, [b] a boolean that is true
    when the matrix is known positive definite and [m] a s x s matrix.

    Prints a message on standard error and raises [Report.Error] in case
    something bad happens. *)
val file : string -> (int * bool * float list list) list
