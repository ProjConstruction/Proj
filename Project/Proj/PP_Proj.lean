import Lean.Data.Options

register_option proj_pp : Bool :=
  { defValue := false,
    descr := "pretty print `Proj`" }
