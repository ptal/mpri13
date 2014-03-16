type name = Name of string

type dname = DName of string

type lname = LName of string

type tname = TName of string

let lower_tname (TName x) = TName (String.lowercase x)
